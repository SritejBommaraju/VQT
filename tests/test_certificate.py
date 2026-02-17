import json
import pytest
from vqt.dsl.builder import simple_circuit
from vqt.optimization.passes import GateCancellationPass
from vqt.certification.equivalence import EquivalenceChecker, EquivalenceReport
from vqt.certification.certifier import Certifier, CertificateSigner
from vqt.compiler.simulator import NativeSimulator

sim = NativeSimulator()


def _make_cert():
    b = simple_circuit(2, "cert_test")
    b.h(0)
    b.cx(0, 1)
    circuit = b.build()

    opt_pass = GateCancellationPass()
    opt = opt_pass.run(circuit)

    sv = sim.run(opt)
    checker = EquivalenceChecker()
    report = checker.check(opt, sv, "native")

    certifier = Certifier()
    cert = certifier.generate(circuit, opt, opt_pass.trace, report, {"00": 50, "11": 50})
    return cert


class TestCertificateSigning:
    def test_sign_and_verify(self):
        cert = _make_cert()
        signer = CertificateSigner("test-key")
        envelope = signer.sign(cert)

        assert "signature" in envelope
        assert "certificate" in envelope
        assert signer.verify(envelope)

    def test_tamper_detection(self):
        cert = _make_cert()
        signer = CertificateSigner("test-key")
        envelope = signer.sign(cert)

        # Tamper with the certificate
        envelope["certificate"]["circuit_name"] = "TAMPERED"
        assert not signer.verify(envelope)

    def test_wrong_key_fails(self):
        cert = _make_cert()
        signer1 = CertificateSigner("key-1")
        signer2 = CertificateSigner("key-2")
        envelope = signer1.sign(cert)
        assert not signer2.verify(envelope)

    def test_cert_json_roundtrip(self):
        cert = _make_cert()
        payload = cert.to_canonical_json()
        data = json.loads(payload)
        assert data["circuit_name"] == "cert_test"
        assert "original_ir_hash" in data
