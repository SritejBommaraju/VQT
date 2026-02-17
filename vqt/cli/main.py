import argparse
import sys
import json
from vqt.dsl.builder import simple_circuit
from vqt.optimization.passes import GateCancellationPass
from vqt.backends.qiskit_interface import run_on_qiskit, QiskitInterface
from vqt.certification.equivalence import EquivalenceChecker
from vqt.certification.certifier import Certifier
from vqt.compiler.simulator import NativeSimulator

def certify_demo():
    print("=== VQT Certification Pipeline ===")
    
    # 1. Define Circuit (Standard Bell State)
    print("[1] Building Circuit...")
    b = simple_circuit(2, "certified_bell")
    b.h(0)
    b.cx(0, 1) 
    # Add a redundant pair to test optimization
    b.x(0)
    b.x(0) 
    circuit = b.build()
    print(f"    Original Hash: {circuit.digest()}")
    
    # 2. Optimization
    print("[2] Running Verified Optimizations...")
    optimizer = GateCancellationPass()
    opt_circuit = optimizer.run(circuit)
    print(f"    Optimized Hash: {opt_circuit.digest()}")
    print(f"    Trace: {len(optimizer.trace.steps)} proof objects generated")
    
    # 3. Execution (Qiskit)
    print("[3] Executing on Qiskit Backend...")
    try:
        from vqt.backends.qiskit_interface import QiskitInterface
        # We need statevector for equivalence check, but counts for result
        # For prototype, let's just get counts and simulate statevector separately using Qiskit helper if possible
        # Or just trust NativeSimulator for ground truth and compare counts if meaningful.
        # Strict equivalence check requires statevectors.
        
        # Let's run Qiskit Statevector for equivalence
        from qiskit import Aer, execute
        qi = QiskitInterface()
        qk_circ = qi.to_qiskit(opt_circuit)
        # Remove measurements for statevector sim
        qk_circ.remove_final_measurements() 
        sim_state = Aer.get_backend('statevector_simulator')
        job = execute(qk_circ, sim_state)
        result = job.result()
        qiskit_sv = result.get_statevector()
        
        # 4. Equivalence Check
        print("[4] Verifying Semantic Equivalence...")
        checker = EquivalenceChecker()
        report = checker.check(opt_circuit, qiskit_sv, "qiskit_statevector")
        print(f"    Fidelity: {report.fidelity:.6f}")
        print(f"    Equivalent: {report.is_equivalent}")
        
        # 5. Result Generation (Counts)
        # Add measurements back for counts
        qk_circ_meas = qi.to_qiskit(opt_circuit) 
        sim_qasm = Aer.get_backend('qasm_simulator')
        job_qasm = execute(qk_circ_meas, sim_qasm, shots=1024)
        counts = job_qasm.result().get_counts()
        
    except ImportError as e:
        print(f"    Qiskit error: {e}")
        return

    # 6. Certification
    print("[5] Generating Execution Certificate...")
    certifier = Certifier()
    cert = certifier.generate(
        original_circuit=circuit,
        optimized_circuit=opt_circuit,
        opt_trace=optimizer.trace,
        equiv_report=report,
        backend_results=counts
    )
    
    cert_hash = cert.digest()
    print(f"    Certificate Hash: {cert_hash}")
    
    filename = "execution_certificate.json"
    with open(filename, "w") as f:
        f.write(cert.to_canonical_json())
    print(f"    Saved to {filename}")

if __name__ == "__main__":
    certify_demo()
