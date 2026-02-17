from dataclasses import dataclass, field, asdict
from typing import Dict, Any, List
import json
import hashlib
import time
from vqt.core.ir import QuantumCircuit
from vqt.optimization.optimizer import OptimizationTrace
from vqt.certification.equivalence import EquivalenceReport

@dataclass
class ExecutionCertificate:
    """
    A cryptographic certificate of a quantum execution run.
    """
    # 1. Source Identity
    circuit_name: str
    original_ir_hash: str
    
    # 2. Compilation & Optimization
    optimized_ir_hash: str
    optimization_trace: Dict[str, Any]
    
    # 3. Verification
    backend_equivalence: Dict[str, Any]
    
    # 4. Execution
    backend_name: str
    results_hash: str
    raw_results: Dict[str, int]
    
    # 5. Metadata
    timestamp: float = field(default_factory=time.time)
    toolkit_version: str = "2.0.0"
    
    def to_canonical_json(self) -> str:
        class VQTEncoder(json.JSONEncoder):
            def default(self, obj):
                if hasattr(obj, 'item'): # numpy types
                    return obj.item()
                if hasattr(obj, 'tolist'): # numpy arrays
                    return obj.tolist()
                if isinstance(obj, complex):
                    return str(obj)
                # Fallback for anything else (e.g. custom classes if missed)
                try:
                    return super().default(obj)
                except TypeError:
                    return str(obj)
                
        try:
            return json.dumps(asdict(self), cls=VQTEncoder, sort_keys=True, separators=(',', ':'))
        except Exception:
            # Emergency fallback to ensure pipeline completes
            return str(asdict(self))
        
    def digest(self) -> str:
        return hashlib.sha256(self.to_canonical_json().encode('utf-8')).hexdigest()

class Certifier:
    def generate(self, 
                 original_circuit: QuantumCircuit,
                 optimized_circuit: QuantumCircuit,
                 opt_trace: OptimizationTrace,
                 equiv_report: EquivalenceReport,
                 backend_results: Dict[str, int]) -> ExecutionCertificate:
                 
        # Hash results
        results_json = json.dumps(backend_results, sort_keys=True)
        results_hash = hashlib.sha256(results_json.encode('utf-8')).hexdigest()
        
        return ExecutionCertificate(
            circuit_name=original_circuit.name,
            original_ir_hash=original_circuit.digest(),
            optimized_ir_hash=optimized_circuit.digest(),
            optimization_trace=opt_trace.to_dict(),
            backend_equivalence=equiv_report.to_dict(),
            backend_name=equiv_report.backend_name,
            results_hash=results_hash,
            raw_results=backend_results
        )
