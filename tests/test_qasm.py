"""Tests for the OpenQASM 2.0 parser and exporter."""

import math
import numpy as np
import pytest
from vqt.qasm.parser import QASMParser, QASMParseError, parse_qasm, circuit_to_qasm
from vqt.compiler.simulator import NativeSimulator
from vqt.dsl.builder import simple_circuit


class TestQASMParser:
    def test_parse_bell_state(self):
        qasm = """
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg q[2];
        creg c[2];
        h q[0];
        cx q[0], q[1];
        """
        circuit = parse_qasm(qasm, "bell")
        assert circuit.name == "bell"
        assert circuit.num_qubits == 2
        assert circuit.gate_count == 2
        assert circuit.instructions[0].gate.name == 'h'
        assert circuit.instructions[1].gate.name == 'cx'

    def test_parse_measure(self):
        qasm = """
        OPENQASM 2.0;
        qreg q[2];
        creg c[2];
        h q[0];
        measure q[0] -> c[0];
        measure q[1] -> c[1];
        """
        circuit = parse_qasm(qasm, "measure_test")
        assert circuit.gate_count == 3  # h + 2 measures
        assert circuit.instructions[1].gate.name == 'measure'
        assert circuit.instructions[1].clbits[0].index == 0
        assert circuit.instructions[2].clbits[0].index == 1

    def test_parse_rz_with_pi(self):
        qasm = """
        OPENQASM 2.0;
        qreg q[1];
        creg c[1];
        rz(pi/4) q[0];
        """
        circuit = parse_qasm(qasm)
        assert circuit.gate_count == 1
        assert circuit.instructions[0].gate.name == 'rz'
        assert abs(circuit.instructions[0].gate.params[0] - math.pi / 4) < 1e-10

    def test_parse_multiple_registers(self):
        qasm = """
        OPENQASM 2.0;
        qreg a[2];
        qreg b[1];
        creg ca[2];
        h a[0];
        x b[0];
        """
        circuit = parse_qasm(qasm, "multi_reg")
        assert circuit.num_qubits == 3
        assert len(circuit.qregs) == 2
        assert circuit.instructions[0].qubits[0].register_name == 'a'
        assert circuit.instructions[1].qubits[0].register_name == 'b'

    def test_parse_comments_stripped(self):
        qasm = """
        OPENQASM 2.0;
        // This is a comment
        qreg q[1];
        creg c[1];
        h q[0]; // inline comment
        """
        circuit = parse_qasm(qasm)
        assert circuit.gate_count == 1

    def test_invalid_version_raises_error(self):
        qasm = """
        OPENQASM 3.0;
        qreg q[1];
        """
        with pytest.raises(QASMParseError, match="Unsupported QASM version"):
            parse_qasm(qasm)

    def test_unknown_gate_raises_error(self):
        qasm = """
        OPENQASM 2.0;
        qreg q[1];
        creg c[1];
        foo q[0];
        """
        with pytest.raises(QASMParseError, match="Unknown gate"):
            parse_qasm(qasm)

    def test_roundtrip_bell_state(self):
        """Build with DSL -> export to QASM -> parse back -> simulate -> compare."""
        b = simple_circuit(2, "bell_rt")
        b.h(0)
        b.cx(0, 1)
        orig_circuit = b.build()

        sim = NativeSimulator()
        orig_sv = sim.run(orig_circuit)

        qasm_str = circuit_to_qasm(orig_circuit)
        parsed = parse_qasm(qasm_str, "bell_parsed")
        parsed_sv = sim.run(parsed)

        assert np.allclose(orig_sv, parsed_sv, atol=1e-10)

    def test_roundtrip_rz_gate(self):
        """Roundtrip for RZ gate preserves parameter."""
        b = simple_circuit(1, "rz_rt")
        b.rz(0, math.pi / 4)
        orig = b.build()

        qasm_str = circuit_to_qasm(orig)
        parsed = parse_qasm(qasm_str, "rz_parsed")

        sim = NativeSimulator()
        assert np.allclose(sim.run(orig), sim.run(parsed), atol=1e-10)

    def test_export_format(self):
        """Verify QASM export produces correct format."""
        b = simple_circuit(2, "export_test")
        b.h(0)
        b.cx(0, 1)
        circuit = b.build()

        qasm = circuit_to_qasm(circuit)
        assert 'OPENQASM 2.0;' in qasm
        assert 'qreg q[2];' in qasm
        assert 'h q[0];' in qasm
        assert 'cx q[0], q[1];' in qasm

    def test_export_rz_uses_pi_notation(self):
        b = simple_circuit(1, "rz_export")
        b.rz(0, math.pi / 4)
        circuit = b.build()

        qasm = circuit_to_qasm(circuit)
        assert 'pi/4' in qasm

    def test_parse_all_single_gates(self):
        qasm = """
        OPENQASM 2.0;
        qreg q[1];
        creg c[1];
        h q[0];
        x q[0];
        y q[0];
        z q[0];
        s q[0];
        t q[0];
        """
        circuit = parse_qasm(qasm)
        assert circuit.gate_count == 6
        names = [i.gate.name for i in circuit.instructions]
        assert names == ['h', 'x', 'y', 'z', 's', 't']

    def test_parse_swap_gate(self):
        qasm = """
        OPENQASM 2.0;
        qreg q[2];
        creg c[2];
        swap q[0], q[1];
        """
        circuit = parse_qasm(qasm)
        assert circuit.gate_count == 1
        assert circuit.instructions[0].gate.name == 'swap'
