import pytest
from vqt.core.ir import (
    QuantumCircuit, QuantumRegister, ClassicalRegister,
    Gate, Qubit, Clbit, Instruction,
)


def _make_circuit(n: int = 2, name: str = "test") -> QuantumCircuit:
    qc = QuantumCircuit(name)
    qc.add_qreg("q", n)
    qc.add_creg("c", n)
    return qc


class TestHashing:
    def test_deterministic_hash(self):
        """Same circuit built twice must produce identical digest."""
        c1 = _make_circuit()
        c1.append(Gate("h", 1), [Qubit("q", 0)])
        c2 = _make_circuit()
        c2.append(Gate("h", 1), [Qubit("q", 0)])
        assert c1.digest() == c2.digest()

    def test_different_circuits_differ(self):
        c1 = _make_circuit()
        c1.append(Gate("h", 1), [Qubit("q", 0)])
        c2 = _make_circuit()
        c2.append(Gate("x", 1), [Qubit("q", 0)])
        assert c1.digest() != c2.digest()


class TestValidation:
    def test_gate_arity_mismatch(self):
        qc = _make_circuit()
        with pytest.raises(ValueError, match="expects 1 qubits"):
            qc.append(Gate("h", 1), [Qubit("q", 0), Qubit("q", 1)])

    def test_qubit_out_of_bounds(self):
        qc = _make_circuit()
        with pytest.raises(IndexError, match="out of bounds"):
            qc.append(Gate("h", 1), [Qubit("q", 5)])

    def test_unknown_register(self):
        qc = _make_circuit()
        with pytest.raises(ValueError, match="not found"):
            qc.append(Gate("h", 1), [Qubit("nonexistent", 0)])


class TestMetrics:
    def test_num_qubits(self):
        qc = _make_circuit(3)
        assert qc.num_qubits == 3

    def test_gate_count(self):
        qc = _make_circuit()
        qc.append(Gate("h", 1), [Qubit("q", 0)])
        qc.append(Gate("cx", 2), [Qubit("q", 0), Qubit("q", 1)])
        assert qc.gate_count == 2

    def test_gate_count_by_type(self):
        qc = _make_circuit()
        qc.append(Gate("h", 1), [Qubit("q", 0)])
        qc.append(Gate("h", 1), [Qubit("q", 1)])
        qc.append(Gate("cx", 2), [Qubit("q", 0), Qubit("q", 1)])
        assert qc.gate_count_by_type() == {"h": 2, "cx": 1}

    def test_depth_parallel(self):
        """Two H gates on different qubits have depth 1."""
        qc = _make_circuit()
        qc.append(Gate("h", 1), [Qubit("q", 0)])
        qc.append(Gate("h", 1), [Qubit("q", 1)])
        assert qc.depth == 1

    def test_depth_sequential(self):
        """H then CX on qubit 0 gives depth 2."""
        qc = _make_circuit()
        qc.append(Gate("h", 1), [Qubit("q", 0)])
        qc.append(Gate("cx", 2), [Qubit("q", 0), Qubit("q", 1)])
        assert qc.depth == 2

    def test_depth_empty(self):
        qc = _make_circuit()
        assert qc.depth == 0
