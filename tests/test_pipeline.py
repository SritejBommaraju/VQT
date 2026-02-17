import numpy as np
import pytest
from vqt.dsl.builder import simple_circuit
from vqt.optimization.passes import GateCancellationPass, IdentityRemovalPass
from vqt.certification.equivalence import EquivalenceChecker
from vqt.certification.certifier import Certifier, CertificateSigner
from vqt.compiler.simulator import NativeSimulator


class TestFullPipeline:
    def test_bell_state_pipeline(self):
        """Build -> Optimize -> Simulate -> Equivalence Check -> Certify"""
        # 1. Build
        b = simple_circuit(2, "pipeline_bell")
        b.h(0)
        b.cx(0, 1)
        b.x(0)
        b.x(0)  # redundant pair
        circuit = b.build()
        assert circuit.gate_count == 4

        # 2. Optimize
        opt_pass = GateCancellationPass()
        opt = opt_pass.run(circuit)
        assert opt.gate_count == 2  # X pair removed

        # 3. Simulate
        sim = NativeSimulator()
        sv_orig = sim.run(circuit)
        sv_opt = sim.run(opt)
        assert np.allclose(sv_orig, sv_opt)

        # 4. Equivalence
        checker = EquivalenceChecker()
        report = checker.check(opt, sv_opt, "native")
        assert report.is_equivalent

        # 5. Certify
        certifier = Certifier()
        cert = certifier.generate(circuit, opt, opt_pass.trace, report, {"00": 50, "11": 50})
        assert cert.circuit_name == "pipeline_bell"
        assert len(cert.digest()) == 64  # SHA-256 hex

        # 6. Sign
        signer = CertificateSigner()
        envelope = signer.sign(cert)
        assert signer.verify(envelope)

    def test_chained_optimization_passes(self):
        """IdentityRemoval -> GateCancellation preserves semantics."""
        b = simple_circuit(2, "chained")
        b.h(0)
        b.rz(0, 0.0)  # identity
        b.x(1)
        b.x(1)  # cancels
        b.cx(0, 1)
        circuit = b.build()
        assert circuit.gate_count == 5

        sim = NativeSimulator()
        sv_orig = sim.run(circuit)

        c1 = IdentityRemovalPass().run(circuit)
        assert c1.gate_count == 4  # RZ(0) removed

        c2 = GateCancellationPass().run(c1)
        assert c2.gate_count == 2  # X pair removed

        sv_final = sim.run(c2)
        assert np.allclose(sv_orig, sv_final)
