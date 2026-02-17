from dataclasses import dataclass, field, asdict
from typing import Dict, Any, List
import json
import hashlib
import hmac
import time
import numpy as np
from vqt.core.ir import QuantumCircuit
from vqt.optimization.optimizer import OptimizationTrace
from vqt.certification.equivalence import EquivalenceReport

def deep_sanitize(obj):
    """Recursively convert numpy types to native python types."""
    if isinstance(obj, (np.integer, int)):
        return int(obj)
    if isinstance(obj, (np.floating, float)):
        return float(obj)
    if isinstance(obj, (np.bool_, bool)):
        return bool(obj)
    if isinstance(obj, (np.ndarray, list, tuple)):
        return [deep_sanitize(x) for x in obj]
    if isinstance(obj, dict):
        return {str(k): deep_sanitize(v) for k, v in obj.items()} 
    if isinstance(obj, complex):
        return str(obj)
    if obj is None:
        return None
    return obj

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
    # 6. Formal Verification
    verification_data: Dict[str, Any] = field(default_factory=dict)
    
    timestamp: float = field(default_factory=time.time)
    toolkit_version: str = "2.0.0"
    
    def to_canonical_json(self) -> str:
        # Since we satisfy everything in generate, standard json.dumps works.
        # But we keep VQTEncoder structure just in case.
        return json.dumps(asdict(self), sort_keys=True, separators=(',', ':'))
        
    def digest(self) -> str:
        return hashlib.sha256(self.to_canonical_json().encode('utf-8')).hexdigest()

    def to_json_file(self, filepath: str) -> None:
        with open(filepath, 'w') as f:
            f.write(self.to_canonical_json())

class Certifier:
    def generate(self, 
                 original_circuit: QuantumCircuit,
                 optimized_circuit: QuantumCircuit,
                 opt_trace: OptimizationTrace,
                 equiv_report: EquivalenceReport,
                 backend_results: Dict[str, int],
                 verification_data: Dict[str, Any] = None) -> ExecutionCertificate:
                 
        if verification_data is None:
            verification_data = {"status": "skipped"}

        # Sanitize everything deeply
        safe_opt_trace = deep_sanitize(opt_trace.to_dict())
        safe_equiv_report = deep_sanitize(equiv_report.to_dict())
        safe_backend_results = deep_sanitize(backend_results)
        safe_verification_data = deep_sanitize(verification_data)

        # Hash results (deterministic)
        results_json = json.dumps(safe_backend_results, sort_keys=True)
        results_hash = hashlib.sha256(results_json.encode('utf-8')).hexdigest()
        
        return ExecutionCertificate(
            circuit_name=str(original_circuit.name),
            original_ir_hash=str(original_circuit.digest()),
            optimized_ir_hash=str(optimized_circuit.digest()),
            optimization_trace=safe_opt_trace,
            backend_equivalence=safe_equiv_report,
            backend_name=str(equiv_report.backend_name),
            results_hash=results_hash,
            raw_results=safe_backend_results,
            verification_data=safe_verification_data
        )


class CertificateSigner:
    """HMAC-SHA256 signing and verification for execution certificates."""

    def __init__(self, secret_key: str = "vqt-default-key"):
        self._key = secret_key.encode('utf-8')

    def sign(self, cert: ExecutionCertificate) -> Dict[str, Any]:
        payload = cert.to_canonical_json()
        sig = hmac.new(self._key, payload.encode('utf-8'), hashlib.sha256).hexdigest()
        return {
            "certificate": json.loads(payload),
            "signature": sig,
            "algorithm": "HMAC-SHA256",
        }

    def verify(self, envelope: Dict[str, Any]) -> bool:
        payload = json.dumps(envelope["certificate"], sort_keys=True, separators=(',', ':'))
        expected = hmac.new(self._key, payload.encode('utf-8'), hashlib.sha256).hexdigest()
        return hmac.compare_digest(expected, envelope.get("signature", ""))

    def sign_to_file(self, cert: ExecutionCertificate, filepath: str) -> None:
        envelope = self.sign(cert)
        with open(filepath, 'w') as f:
            json.dump(envelope, f, indent=2, sort_keys=True)
