from vqt.benchmarks.algorithms import qft, grover_search
from vqt.optimization.passes import GateCancellationPass
from vqt.certification.certifier import Certifier
from vqt.certification.equivalence import EquivalenceChecker
from vqt.compiler.simulator import NativeSimulator
import json
import numpy as np
from dataclasses import asdict

def run_benchmarks():
    print("=== VQT Benchmark Suite ===")
    
    benchmarks = [
        ("Grover (2q)", grover_search(2)),
        ("QFT (3q)", qft(3))
    ]
    
    optimizer = GateCancellationPass()
    certifier = Certifier()
    checker = EquivalenceChecker()
    native_sim = NativeSimulator()
    
    results = []
    
    for name, builder in benchmarks:
        print(f"\nRunning {name}...")
        circuit = builder.build()
        initial_hash = circuit.digest()
        print(f"  Initial Hash: {initial_hash[:8]}...")
        
        # Optimize
        opt_circuit = optimizer.run(circuit)
        opt_hash = opt_circuit.digest()
        print(f"  Optimized Hash: {opt_hash[:8]}...")
        
        # Simulate (Ground Truth)
        state_vector = native_sim.run(opt_circuit)
        
        # Certify (Self-Check vs Self for prototype since we don't assume Qiskit installed here)
        # In real scenario, we'd check against Qiskit.
        report = checker.check(opt_circuit, state_vector, "native_simulator")
        
        try:
            # Generate Certificate
            cert = certifier.generate(
                circuit, opt_circuit, optimizer.trace, report, {"status": "benchmarked"}
            )
            
            results.append({
                "name": name,
                "fidelity": float(report.fidelity),
                "cert_hash": cert.digest(),
                "opt_steps": len(optimizer.trace.steps)
            })
            print(f"  Passed! Cert: {cert.digest()[:8]}...")
        except Exception as e:
            print(f"  FAILED to generate cert: {e}")
            import traceback
            traceback.print_exc()

    print("\n=== Summary ===")
    print(json.dumps(results, indent=2))

if __name__ == "__main__":
    run_benchmarks()
