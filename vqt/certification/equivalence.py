import numpy as np
from dataclasses import dataclass, asdict
from typing import Dict, Any
from vqt.core.ir import QuantumCircuit
from vqt.compiler.simulator import NativeSimulator
# We will import Qiskit runner dynamically to avoid circular deps or hard deps

@dataclass
class EquivalenceReport:
    circuit_name: str
    circuit_hash: str
    backend_name: str
    fidelity: float
    is_equivalent: bool
    tolerance: float = 1e-6
    
    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

class EquivalenceChecker:
    def __init__(self, tolerance: float = 1e-6):
        self.native_sim = NativeSimulator()
        self.tolerance = tolerance
        
    def check(self, circuit: QuantumCircuit, external_vector: np.ndarray, backend_name: str) -> EquivalenceReport:
        # Run trusted simulation
        native_vector = self.native_sim.run(circuit)
        
        # Calculate Fidelity for pure states: |<psi|phi>|^2
        overlap = np.dot(np.conj(native_vector), external_vector)
        fidelity = float(np.abs(overlap) ** 2)
        
        is_equivalent = bool(np.isclose(fidelity, 1.0, atol=self.tolerance))
        
        return EquivalenceReport(
            circuit_name=str(circuit.name),
            circuit_hash=str(circuit.digest()),
            backend_name=str(backend_name),
            fidelity=fidelity,
            is_equivalent=is_equivalent,
            tolerance=float(self.tolerance)
        )
