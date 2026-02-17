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
        self.Z = np.array([[1, 0], [0, -1]], dtype=complex)
        # Note: Multi-qubit gates are handled via tensor products dynamically

    def run(self, circuit: QuantumCircuit) -> np.ndarray:
        # Determine total qubits
        # Assuming single register for simplicity in this prototype, 
        # or summing sizes. Let's assume linear indexing 0..N-1.
        num_qubits = sum(r.size for r in circuit.qregs)
        state_size = 2 ** num_qubits
        state = np.zeros(state_size, dtype=complex)
        state[0] = 1.0 # Initialize to |0...0>

        for instr in circuit.instructions:
            gate_name = instr.gate.name.lower()
            target_qubits = [q.index for q in instr.qubits] # Simplification: Assuming 1 qreg or global indexing
            
            # Construct full operator matrix
            op_matrix = self._get_operator(gate_name, target_qubits, num_qubits)
            state = op_matrix @ state
            
        return state

    def _get_operator(self, gate_name: str, target_qubits: list, num_qubits: int) -> np.ndarray:
        # Optimization: This is inefficient for large N, but robust for correctness checking of small circuits.
        # We construct the full 2^N x 2^N matrix.
        
        if gate_name == 'cx':
             # CNOT logic is special construction
             # Control: target_qubits[0], Target: target_qubits[1]
             # |00> -> |00>, |01> -> |01>, |10> -> |11>, |11> -> |10>
             # This requires permutation if qubits are not adjacent/ordered.
             # FOR PROTOTYPE: Relying on a simpler tensor product approach for single qubit gates,
             # and a predefined matrix for CNOT if possible, or just applying logic manually to the state vector index.
             pass 
        
        # ACTUALLY, applying gates to statevector index is easier than building giant matrices.
        return self._build_full_matrix(gate_name, target_qubits, num_qubits)

    def _build_full_matrix(self, gate_name: str, targets: list, n: int) -> np.ndarray:
        # Naive tensor product construction
        if gate_name in ['h', 'x', 'z']:
            # Tensor product: I x ... x G x ... x I
            target = targets[0]
            mats = [self.I] * n
            if gate_name == 'h': mats[target] = self.H
            elif gate_name == 'x': mats[target] = self.X
            elif gate_name == 'z': mats[target] = self.Z
            
            full_op = mats[0]
            for m in mats[1:]:
                full_op = np.kron(full_op, m) # Note: Qiskit uses reverse order (qubit 0 is rightmost in tensor). 
                # VQT needs to define its convention. Let's stick to standard math: qubit 0 is left (or adjust to match Qiskit).
                # Let's adopt Qiskit convention: q0 is LSB. so M_n x ... x M_0.
            
            # To match Qiskit: kron(mats[n-1], ... mats[0])
            full_op = mats[n-1]
            for i in range(n-2, -1, -1):
                full_op = np.kron(full_op, mats[i])
                
            return full_op

        elif gate_name == 'cx':
            # CNOT matrix construction
            c, t = targets
            # Projectors
            P0 = np.array([[1, 0], [0, 0]], dtype=complex)
            P1 = np.array([[0, 0], [0, 1]], dtype=complex)
            
            # Op = P0_c x I_t + P1_c x X_t
            # Again, assume Qiskit order (q0 is LSB)
            term1_mats = [self.I] * n
            term1_mats[c] = P0
            
            term2_mats = [self.I] * n
            term2_mats[c] = P1
            term2_mats[t] = self.X
            
            # Build term 1
            op1 = term1_mats[n-1]
            for i in range(n-2, -1, -1):
                op1 = np.kron(op1, term1_mats[i])
                
            # Build term 2
            op2 = term2_mats[n-1]
            for i in range(n-2, -1, -1):
                op2 = np.kron(op2, term2_mats[i])
                
            return op1 + op2
            
        elif gate_name == 'swap':
             # SWAP logic similar to CNOT
             # Op = P0 P0 + P0 P1 (swap? no) ... 
             # SWAP = CX(1,2) CX(2,1) CX(1,2)
             # Let's just implement basic H, X, Z, CX for now to prove point.
             pass

        return np.eye(2**n, dtype=complex)

