"""Tests for the HTML dashboard generator."""

import pytest
from vqt.dsl.builder import simple_circuit
from vqt.compiler.simulator import NativeSimulator
from vqt.optimization.passes import GateCancellationPass
from vqt.certification.equivalence import EquivalenceChecker
from vqt.certification.certifier import Certifier, CertificateSigner
from vqt.dashboard.generator import circuit_to_ascii, generate_dashboard


class TestCircuitASCII:
    def test_empty_circuit(self):
        b = simple_circuit(2, "empty")
        circuit = b.build()
        ascii_art = circuit_to_ascii(circuit)
        assert 'q[0]' in ascii_art
        assert 'q[1]' in ascii_art

    def test_single_h_gate(self):
        b = simple_circuit(1, "single_h")
        b.h(0)
        circuit = b.build()
        ascii_art = circuit_to_ascii(circuit)
        assert 'H' in ascii_art
        assert 'q[0]' in ascii_art

    def test_bell_state_ascii(self):
        b = simple_circuit(2, "bell_ascii")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()
        ascii_art = circuit_to_ascii(circuit)
        assert 'H' in ascii_art
        assert '*' in ascii_art  # control
        assert 'X' in ascii_art  # target

    def test_alignment_two_qubits(self):
        """Both qubit lines should have content."""
        b = simple_circuit(2, "align")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()
        ascii_art = circuit_to_ascii(circuit)
        lines = ascii_art.strip().split('\n')
        assert len(lines) == 2


class TestDashboard:
    def _build_pipeline(self):
        """Helper: run full pipeline and return all artifacts."""
        b = simple_circuit(2, "dashboard_bell")
        b.h(0)
        b.cx(0, 1)
        b.x(0)
        b.x(0)
        original = b.build()

        opt_pass = GateCancellationPass()
        optimized = opt_pass.run(original)

        sim = NativeSimulator()
        sv = sim.run(optimized)

        checker = EquivalenceChecker()
        report = checker.check(optimized, sv, "native")

        certifier = Certifier()
        cert = certifier.generate(original, optimized, opt_pass.trace, report, {"00": 50, "11": 50})

        signer = CertificateSigner()
        envelope = signer.sign(cert)
        sig_valid = signer.verify(envelope)

        return original, optimized, opt_pass.trace, report, cert, envelope, sig_valid

    def test_dashboard_valid_html(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert '<!DOCTYPE html>' in html
        assert '</html>' in html

    def test_dashboard_contains_circuits(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert 'Original Circuit' in html
        assert 'Optimized Circuit' in html

    def test_dashboard_contains_gate_counts(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert 'Gate Count Comparison' in html
        assert '<svg' in html  # SVG bar chart

    def test_dashboard_contains_fidelity(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert 'Fidelity' in html
        assert 'PASS' in html

    def test_dashboard_contains_hashes(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert cert.original_ir_hash[:12] in html
        assert cert.optimized_ir_hash[:12] in html

    def test_dashboard_contains_certified_stamp(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert 'CERTIFIED' in html

    def test_dashboard_signature_status(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, sig_valid)
        assert 'SIGNATURE VALID' in html

    def test_dashboard_invalid_signature(self):
        original, optimized, trace, report, cert, envelope, sig_valid = self._build_pipeline()
        html = generate_dashboard(original, optimized, trace, report, cert, envelope, signature_valid=False)
        assert 'SIGNATURE INVALID' in html
