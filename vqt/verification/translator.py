from vqt.core.ir import QuantumCircuit, Instruction

class CoqTranslator:
    def __init__(self, circuit: QuantumCircuit):
        self.circuit = circuit

    def translate(self) -> str:
        coq_code = []
        coq_code.append("Require Import QuantumLib.")
        coq_code.append("Import ListNotations.")
        coq_code.append("")
        coq_code.append(f"Definition {self.circuit.name}_circuit : Circuit := [")
        
        instructions = []
        for instr in self.circuit.instructions:
            gate_name = instr.gate.name.lower()
            qubit_indices = [str(q.index) for q in instr.qubits]
            coq_qubits = f"[{'; '.join(qubit_indices)}]"
            
            if gate_name == 'h':
                instructions.append(f"  mkInstruction H_Gate {coq_qubits}")
            elif gate_name == 'x':
                instructions.append(f"  mkInstruction X_Gate {coq_qubits}")
            elif gate_name == 'z':
                instructions.append(f"  mkInstruction Z_Gate {coq_qubits}")
            elif gate_name == 'cx':
                instructions.append(f"  mkInstruction CNOT_Gate {coq_qubits}")
            elif gate_name == 'swap':
                instructions.append(f"  mkInstruction SWAP_Gate {coq_qubits}")
            # Handling measurement as a no-op for now in Coq verification logic, 
            # or we could add a Measure_Gate type if needed.
            
        coq_code.append(";\n".join(instructions))
        coq_code.append("].")
        
        return "\n".join(coq_code)

def to_coq(circuit: QuantumCircuit) -> str:
    translator = CoqTranslator(circuit)
    return translator.translate()
