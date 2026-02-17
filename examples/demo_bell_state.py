from vqt.dsl.builder import simple_circuit
from vqt.verification.translator import to_coq
try:
    from vqt.backends.qiskit_interface import run_on_qiskit
    QISKIT_AVAILABLE = True
except ImportError:
    QISKIT_AVAILABLE = False

def main():
    print("=== Verified Quantum Toolkit (VQT) Demo ===")
    
    # 1. Define Circuit (Bell State: |00> + |11>)
    print("\n[1] Defining Bell State Circuit...")
    builder = simple_circuit(num_qubits=2, name="bell_state")
    builder.h(0)          # H on qubit 0
    builder.cx(0, 1)      # CNOT from 0 to 1
    builder.measure(0, 0) # Measure qubit 0 -> clbit 0
    builder.measure(1, 1) # Measure qubit 1 -> clbit 1
    
    circuit = builder.build()
    print(f"    Circuit created: {circuit}")

    # 2. Generate Verification Artifact
    print("\n[2] Generating Coq Verification Code...")
    coq_code = to_coq(circuit)
    filename = "bell_state.v"
    with open(filename, "w") as f:
        f.write(coq_code)
    print(f"    Coq code written to '{filename}'.")
    print("    Snippet:")
    print("    " + coq_code.split("\n")[3]) # Print definition line

    # 3. Simulate (if Qiskit is available)
    print("\n[3] Simulating on Qiskit Backend...")
    if QISKIT_AVAILABLE:
        try:
            counts = run_on_qiskit(circuit, shots=1024)
            print(f"    Simulation Results: {counts}")
            # Verify approximate Bell State results (should be ~50% '00' and ~50% '11')
            total = sum(counts.values())
            p00 = counts.get('00', 0) / total
            p11 = counts.get('11', 0) / total
            print(f"    Probabilities: P(|00>)={p00:.2f}, P(|11>)={p11:.2f}")
        except Exception as e:
            print(f"    Simulation failed: {e}")
    else:
        print("    Qiskit not installed/detected. Skipping simulation.")

if __name__ == "__main__":
    main()
