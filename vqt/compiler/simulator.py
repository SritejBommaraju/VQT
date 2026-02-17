import numpy as np
from vqt.core.ir import QuantumCircuit, Instruction

class NativeSimulator:
    """
    A simple, trusted statevector simulator serving as the Ground Truth.
    """
    def __init__(self):
        # Define gate matrices
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
        """Build full 2^n x 2^n matrix for a single-qubit gate on target qubit.
        Uses Qiskit convention: qubit 0 is LSB (rightmost in tensor product)."""
        mats = [self.I] * n
        mats[target] = gate_matrix
        # Qiskit convention: kron(mats[n-1], ..., mats[0])
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

    def run(self, circuit: QuantumCircuit) -> np.ndarray:
        num_qubits = sum(r.size for r in circuit.qregs)
        state_size = 2 ** num_qubits
        state = np.zeros(state_size, dtype=complex)
        state[0] = 1.0  # Initialize to |0...0>

        for instr in circuit.instructions:
            gate_name = instr.gate.name.lower()
            targets = [q.index for q in instr.qubits]
            params = instr.gate.params

            op_matrix = self._build_full_matrix(gate_name, targets, num_qubits, params)
            state = op_matrix @ state

        return state

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
            # SWAP = CX(a,b) @ CX(b,a) @ CX(a,b)
            a, b = targets
            cx_ab = self._build_cx(a, b, n)
            cx_ba = self._build_cx(b, a, n)
            return cx_ab @ cx_ba @ cx_ab

        if gate_name == 'measure':
            return np.eye(2 ** n, dtype=complex)

        raise ValueError(f"Unknown gate: {gate_name}")
