from vqt.core.ir import QuantumCircuit
try:
    from qiskit import QuantumCircuit as QKCircuit
    from qiskit import QuantumRegister as QKRegister
    from qiskit import ClassicalRegister as QKClassicalRegister
except ImportError:
    QKCircuit = None

class QiskitInterface:
    def __init__(self):
        pass

    def to_qiskit(self, circuit: QuantumCircuit):
        if QKCircuit is None:
            raise ImportError("Qiskit is not installed. Please install it to use this backend.")

        # Create Qiskit circuit
        qk_circuit = QKCircuit()
        
        # Map registers
        qreg_map = {}
        for qreg in circuit.qregs:
            qk_qreg = QKRegister(qreg.size, name=qreg.name)
            qk_circuit.add_register(qk_qreg)
            qreg_map[qreg.name] = qk_qreg

        creg_map = {}
        for creg in circuit.cregs:
            qk_creg = QKClassicalRegister(creg.size, name=creg.name)
            qk_circuit.add_register(qk_creg)
            creg_map[creg.name] = qk_creg

        # Add instructions
        for instr in circuit.instructions:
            gate_name = instr.gate.name.lower()
            
            # Map qubits to Qiskit objects
            qk_qubits = [qreg_map[q.register.name][q.index] for q in instr.qubits]
            qk_clbits = [creg_map[c.register.name][c.index] for c in instr.clbits]

            if gate_name == 'h':
                qk_circuit.h(qk_qubits[0])
            elif gate_name == 'x':
                qk_circuit.x(qk_qubits[0])
            elif gate_name == 'z':
                qk_circuit.z(qk_qubits[0])
            elif gate_name == 'cx':
                qk_circuit.cx(qk_qubits[0], qk_qubits[1])
            elif gate_name == 'swap':
                qk_circuit.swap(qk_qubits[0], qk_qubits[1])
            elif gate_name == 'measure':
                qk_circuit.measure(qk_qubits[0], qk_clbits[0])
            else:
                raise ValueError(f"Gate {gate_name} not supported in Qiskit backend yet.")

        return qk_circuit

def run_on_qiskit(circuit: QuantumCircuit, shots: int = 1024):
    try:
        from qiskit import Aer, execute
    except ImportError:
        raise ImportError("Qiskit Aer is required for simulation.")
        
    qk_circuit = QiskitInterface().to_qiskit(circuit)
    simulator = Aer.get_backend('qasm_simulator')
    job = execute(qk_circuit, simulator, shots=shots)
    result = job.result()
    return result.get_counts(qk_circuit)
