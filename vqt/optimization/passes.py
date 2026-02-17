from typing import List
from vqt.core.ir import QuantumCircuit, Instruction
from vqt.optimization.optimizer import Optimizer, ProofObject, OptimizationTrace

class GateCancellationPass(Optimizer):
    def run(self, circuit: QuantumCircuit) -> QuantumCircuit:
        pre_hash = circuit.digest()
        transformations = []
        
        # Simple optimization: remove adjacent identical self-inverse gates
        # We'll rebuild the instruction list
        new_instructions = []
        skip_next = False
        
        # Self-inverse gates
        self_inverse = {'h', 'x', 'y', 'z', 'cx', 'swap'}

        n = len(circuit.instructions)
        for i in range(n):
            if skip_next:
                skip_next = False
                continue
                
            current_inst = circuit.instructions[i]
            
            # Check if there is a next instruction
            if i + 1 < n:
                next_inst = circuit.instructions[i+1]
                
                # Check criteria: same gate, same qubits, self-inverse
                if (current_inst.gate.name == next_inst.gate.name and
                    current_inst.qubits == next_inst.qubits and
                    current_inst.gate.name in self_inverse):
                    
                    # Optimization found!
                    transformations.append(f"Removed {current_inst.gate.name} pair at indices {i}, {i+1}")
                    skip_next = True # Skip the next one too
                    continue

            # Keep instruction if not cancelled
            new_instructions.append(current_inst)

        # Create new circuit
        optimized_circuit = QuantumCircuit(circuit.name + "_opt")
        optimized_circuit.qregs = circuit.qregs
        optimized_circuit.cregs = circuit.cregs
        optimized_circuit.instructions = new_instructions
        
        post_hash = optimized_circuit.digest()
        
        # Create Proof Object
        proof = ProofObject(
            pass_name="GateCancellation",
            pre_hash=pre_hash,
            post_hash=post_hash,
            transformations=transformations,
            semantic_equivalence_claim="forall G in {H,X,Y,Z,CNOT,SWAP}, G * G = I"
        )
        
        self.trace = OptimizationTrace(pre_hash, post_hash, [proof])
        return optimized_circuit
