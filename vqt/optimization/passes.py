from typing import List, Set
from vqt.core.ir import QuantumCircuit, Instruction
from vqt.optimization.optimizer import Optimizer, ProofObject, OptimizationTrace
import math

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


class IdentityRemovalPass(Optimizer):
    """Removes identity-like gates: RZ(0) and gates named 'id'/'identity'."""

    def run(self, circuit: QuantumCircuit) -> QuantumCircuit:
        pre_hash = circuit.digest()
        transformations = []
        new_instructions = []

        for i, instr in enumerate(circuit.instructions):
            name = instr.gate.name.lower()
            # Remove explicit identity gates
            if name in ('id', 'identity'):
                transformations.append(f"Removed identity gate at index {i}")
                continue
            # Remove RZ(0) — rotation by zero
            if name == 'rz' and instr.gate.params:
                if math.isclose(instr.gate.params[0], 0.0, abs_tol=1e-12):
                    transformations.append(f"Removed RZ(0) at index {i}")
                    continue
            new_instructions.append(instr)

        optimized = QuantumCircuit(circuit.name + "_idrem")
        optimized.qregs = circuit.qregs
        optimized.cregs = circuit.cregs
        optimized.instructions = new_instructions

        post_hash = optimized.digest()
        proof = ProofObject(
            pass_name="IdentityRemoval",
            pre_hash=pre_hash,
            post_hash=post_hash,
            transformations=transformations,
            semantic_equivalence_claim="RZ(0) = I, id = I"
        )
        self.trace = OptimizationTrace(pre_hash, post_hash, [proof])
        return optimized


class CommuteThenCancelPass(Optimizer):
    """Commutes gates to bring cancellable pairs adjacent, then cancels them.

    Conservative commutation rules:
    - Gates on disjoint qubits always commute.
    - Diagonal gates (Z, S, T, RZ) commute on the same qubit.
    """

    DIAGONAL_GATES: Set[str] = {'z', 's', 't', 'rz'}
    SELF_INVERSE: Set[str] = {'h', 'x', 'y', 'z', 'cx', 'swap'}

    def _qubits_of(self, instr: Instruction) -> Set[int]:
        return {q.index for q in instr.qubits}

    def _can_commute(self, a: Instruction, b: Instruction) -> bool:
        qa, qb = self._qubits_of(a), self._qubits_of(b)
        if qa.isdisjoint(qb):
            return True
        na, nb = a.gate.name.lower(), b.gate.name.lower()
        if na in self.DIAGONAL_GATES and nb in self.DIAGONAL_GATES:
            return True
        return False

    def _can_cancel(self, a: Instruction, b: Instruction) -> bool:
        return (a.gate.name == b.gate.name and
                a.qubits == b.qubits and
                a.gate.name.lower() in self.SELF_INVERSE)

    def run(self, circuit: QuantumCircuit) -> QuantumCircuit:
        pre_hash = circuit.digest()
        transformations = []
        instrs = list(circuit.instructions)

        # Bubble-sort style: try to bring cancellable pairs together
        changed = True
        while changed:
            changed = False
            i = 0
            while i < len(instrs) - 1:
                # Check if adjacent pair cancels
                if self._can_cancel(instrs[i], instrs[i + 1]):
                    transformations.append(
                        f"Cancelled {instrs[i].gate.name} pair at positions {i},{i+1}"
                    )
                    instrs.pop(i + 1)
                    instrs.pop(i)
                    changed = True
                    # Don't increment — re-check from same position
                    if i > 0:
                        i -= 1
                    continue

                # Try commuting to expose a cancel
                if (i + 2 < len(instrs) and
                        self._can_commute(instrs[i], instrs[i + 1]) and
                        self._can_cancel(instrs[i], instrs[i + 2])):
                    transformations.append(
                        f"Commuted {instrs[i+1].gate.name} past {instrs[i].gate.name} "
                        f"at positions {i},{i+1}"
                    )
                    instrs[i], instrs[i + 1] = instrs[i + 1], instrs[i]
                    changed = True
                    continue

                i += 1

        optimized = QuantumCircuit(circuit.name + "_commcancel")
        optimized.qregs = circuit.qregs
        optimized.cregs = circuit.cregs
        optimized.instructions = instrs

        post_hash = optimized.digest()
        proof = ProofObject(
            pass_name="CommuteThenCancel",
            pre_hash=pre_hash,
            post_hash=post_hash,
            transformations=transformations,
            semantic_equivalence_claim=(
                "Commutation rules: disjoint qubits commute, "
                "diagonal gates (Z,S,T,RZ) commute on same qubit; "
                "then G*G=I for self-inverse G"
            )
        )
        self.trace = OptimizationTrace(pre_hash, post_hash, [proof])
        return optimized
