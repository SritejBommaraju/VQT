import numpy as np
import pytest
from vqt.core.ir import QuantumCircuit, Gate, Qubit
from vqt.compiler.simulator import NativeSimulator


def _circuit_1q() -> QuantumCircuit:
    qc = QuantumCircuit("sim_test")
    qc.add_qreg("q", 1)
    qc.add_creg("c", 1)
    return qc


def _circuit_2q() -> QuantumCircuit:
    qc = QuantumCircuit("sim_test")
    qc.add_qreg("q", 2)
    qc.add_creg("c", 2)
    return qc


sim = NativeSimulator()


class TestSingleQubitGates:
    def test_x_flips_zero(self):
        """X|0> = |1>"""
        qc = _circuit_1q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])
        sv = sim.run(qc)
        assert np.allclose(sv, [0, 1])

    def test_h_creates_plus(self):
        """H|0> = |+> = (|0>+|1>)/sqrt(2)"""
        qc = _circuit_1q()
        qc.append(Gate("h", 1), [Qubit("q", 0)])
        sv = sim.run(qc)
        assert np.allclose(sv, [1 / np.sqrt(2), 1 / np.sqrt(2)])

    def test_z_phase(self):
        """Z|1> = -|1>"""
        qc = _circuit_1q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])
        qc.append(Gate("z", 1), [Qubit("q", 0)])
        sv = sim.run(qc)
        assert np.allclose(sv, [0, -1])

    def test_y_gate(self):
        """Y|0> = i|1>"""
        qc = _circuit_1q()
        qc.append(Gate("y", 1), [Qubit("q", 0)])
        sv = sim.run(qc)
        assert np.allclose(sv, [0, 1j])

    def test_s_gate(self):
        """S|1> = i|1>"""
        qc = _circuit_1q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])
        qc.append(Gate("s", 1), [Qubit("q", 0)])
        sv = sim.run(qc)
        assert np.allclose(sv, [0, 1j])

    def test_t_gate(self):
        """T|1> = e^(i*pi/4)|1>"""
        qc = _circuit_1q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])
        qc.append(Gate("t", 1), [Qubit("q", 0)])
        sv = sim.run(qc)
        assert np.allclose(sv, [0, np.exp(1j * np.pi / 4)])

    def test_rz(self):
        """RZ(pi)|1> = e^(i*pi/2)|1>"""
        qc = _circuit_1q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])
        qc.append(Gate("rz", 1, [np.pi]), [Qubit("q", 0)])
        sv = sim.run(qc)
        expected = [0, np.exp(1j * np.pi / 2)]
        assert np.allclose(sv, expected)


class TestMultiQubitGates:
    def test_bell_state(self):
        """H(0) CX(0,1) |00> = (|00>+|11>)/sqrt(2)"""
        qc = _circuit_2q()
        qc.append(Gate("h", 1), [Qubit("q", 0)])
        qc.append(Gate("cx", 2), [Qubit("q", 0), Qubit("q", 1)])
        sv = sim.run(qc)
        expected = np.array([1 / np.sqrt(2), 0, 0, 1 / np.sqrt(2)])
        assert np.allclose(sv, expected)

    def test_swap(self):
        """SWAP|10> = |01>"""
        qc = _circuit_2q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])  # |10>
        qc.append(Gate("swap", 2), [Qubit("q", 0), Qubit("q", 1)])
        sv = sim.run(qc)
        # |01> in LSB convention: index 2
        expected = np.array([0, 0, 1, 0])
        assert np.allclose(sv, expected)

    def test_double_swap_identity(self):
        """SWAP twice = identity"""
        qc = _circuit_2q()
        qc.append(Gate("x", 1), [Qubit("q", 0)])
        qc.append(Gate("swap", 2), [Qubit("q", 0), Qubit("q", 1)])
        qc.append(Gate("swap", 2), [Qubit("q", 0), Qubit("q", 1)])
        sv = sim.run(qc)
        # Back to |10> = index 1
        expected = np.array([0, 1, 0, 0])
        assert np.allclose(sv, expected)
