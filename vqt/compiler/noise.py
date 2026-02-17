"""Density matrix noise simulator with depolarizing and amplitude damping channels."""

import numpy as np
from dataclasses import dataclass
from vqt.core.ir import QuantumCircuit


@dataclass
class NoiseConfig:
    """Configuration for noise channels applied after each gate."""
    depolarizing_rate: float = 0.0
    amplitude_damping_rate: float = 0.0


class NoisySimulator:
    """Density matrix simulator with per-gate noise channels."""

    def __init__(self):
        self.I = np.array([[1, 0], [0, 1]], dtype=complex)
        self.H = np.array([[1, 1], [1, -1]], dtype=complex) / np.sqrt(2)
        self.X = np.array([[0, 1], [1, 0]], dtype=complex)
        self.Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
        self.Z = np.array([[1, 0], [0, -1]], dtype=complex)
        self.S = np.array([[1, 0], [0, 1j]], dtype=complex)
        self.T = np.array([[1, 0], [0, np.exp(1j * np.pi / 4)]], dtype=complex)

        self._single_gates = {
            'h': self.H,
            'x': self.X,
            'y': self.Y,
            'z': self.Z,
            's': self.S,
            't': self.T,
        }

    def _rz_matrix(self, theta: float) -> np.ndarray:
        return np.array([
            [np.exp(-1j * theta / 2), 0],
            [0, np.exp(1j * theta / 2)]
        ], dtype=complex)

    def _tensor_single(self, gate_matrix: np.ndarray, target: int, n: int) -> np.ndarray:
        """Build full 2^n x 2^n matrix for a single-qubit gate."""
        mats = [self.I] * n
        mats[target] = gate_matrix
        full_op = mats[n - 1]
        for i in range(n - 2, -1, -1):
            full_op = np.kron(full_op, mats[i])
        return full_op

    def _build_cx(self, control: int, target: int, n: int) -> np.ndarray:
        """Build CNOT matrix using projector decomposition."""
        P0 = np.array([[1, 0], [0, 0]], dtype=complex)
        P1 = np.array([[0, 0], [0, 1]], dtype=complex)

        term1_mats = [self.I] * n
        term1_mats[control] = P0

        term2_mats = [self.I] * n
        term2_mats[control] = P1
        term2_mats[target] = self.X

        op1 = term1_mats[n - 1]
        for i in range(n - 2, -1, -1):
            op1 = np.kron(op1, term1_mats[i])

        op2 = term2_mats[n - 1]
        for i in range(n - 2, -1, -1):
            op2 = np.kron(op2, term2_mats[i])

        return op1 + op2

    def _build_full_matrix(self, gate_name: str, targets: list, n: int,
                           params: list = None) -> np.ndarray:
        if gate_name in self._single_gates:
            return self._tensor_single(self._single_gates[gate_name], targets[0], n)
        if gate_name == 'rz':
            theta = params[0] if params else 0.0
            return self._tensor_single(self._rz_matrix(theta), targets[0], n)
        if gate_name == 'cx':
            return self._build_cx(targets[0], targets[1], n)
        if gate_name == 'swap':
            a, b = targets
            cx_ab = self._build_cx(a, b, n)
            cx_ba = self._build_cx(b, a, n)
            return cx_ab @ cx_ba @ cx_ab
        if gate_name == 'measure':
            return np.eye(2 ** n, dtype=complex)
        raise ValueError(f"Unknown gate: {gate_name}")

    def run(self, circuit: QuantumCircuit, noise_config: NoiseConfig) -> np.ndarray:
        """Simulate circuit with noise, returning a density matrix."""
        n = sum(r.size for r in circuit.qregs)
        dim = 2 ** n

        # Initialize rho = |0...0><0...0|
        rho = np.zeros((dim, dim), dtype=complex)
        rho[0, 0] = 1.0

        for instr in circuit.instructions:
            gate_name = instr.gate.name.lower()
            targets = [q.index for q in instr.qubits]
            params = instr.gate.params

            # Unitary evolution: rho -> U rho U†
            U = self._build_full_matrix(gate_name, targets, n, params)
            rho = U @ rho @ U.conj().T

            # Apply noise to each target qubit (skip measure)
            if gate_name != 'measure':
                for qubit in targets:
                    if noise_config.depolarizing_rate > 0:
                        rho = self._apply_depolarizing(
                            rho, qubit, n, noise_config.depolarizing_rate
                        )
                    if noise_config.amplitude_damping_rate > 0:
                        rho = self._apply_amplitude_damping(
                            rho, qubit, n, noise_config.amplitude_damping_rate
                        )

        return rho

    def _apply_depolarizing(self, rho: np.ndarray, qubit: int, n: int,
                            p: float) -> np.ndarray:
        """Apply depolarizing channel: rho -> (1-p)*rho + (p/3)*(X rho X + Y rho Y + Z rho Z)."""
        X_full = self._tensor_single(self.X, qubit, n)
        Y_full = self._tensor_single(self.Y, qubit, n)
        Z_full = self._tensor_single(self.Z, qubit, n)

        return ((1 - p) * rho
                + (p / 3) * (X_full @ rho @ X_full.conj().T
                             + Y_full @ rho @ Y_full.conj().T
                             + Z_full @ rho @ Z_full.conj().T))

    def _apply_amplitude_damping(self, rho: np.ndarray, qubit: int, n: int,
                                  gamma: float) -> np.ndarray:
        """Apply amplitude damping channel with Kraus operators K0, K1."""
        # K0 = [[1, 0], [0, sqrt(1-gamma)]]
        # K1 = [[0, sqrt(gamma)], [0, 0]]
        K0 = np.array([[1, 0], [0, np.sqrt(1 - gamma)]], dtype=complex)
        K1 = np.array([[0, np.sqrt(gamma)], [0, 0]], dtype=complex)

        K0_full = self._tensor_single(K0, qubit, n)
        K1_full = self._tensor_single(K1, qubit, n)

        return K0_full @ rho @ K0_full.conj().T + K1_full @ rho @ K1_full.conj().T


def fidelity(rho: np.ndarray, target_state: np.ndarray) -> float:
    """Compute fidelity F = <psi|rho|psi> between density matrix and pure state."""
    psi = target_state.reshape(-1, 1)
    return float(np.real(psi.conj().T @ rho @ psi).item())
