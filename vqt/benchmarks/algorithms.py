from vqt.dsl.builder import simple_circuit, CircuitBuilder
import math

def qft(num_qubits: int) -> CircuitBuilder:
    builder = simple_circuit(num_qubits, f"qft_{num_qubits}")
    
    for i in range(num_qubits):
        builder.h(i)
        for j in range(i + 1, num_qubits):
            # Controlled-Phase would go here. 
            # For prototype, we'll substitute CNOT for connectivity check, 
            # or add a CP gate to IR if we had time. 
            # Sticking to H, CX, SWAP for now.
            builder.cx(j, i) 
            
    # Swaps
    for i in range(num_qubits // 2):
        builder.swap(i, num_qubits - 1 - i)
        
    return builder

def grover_search(num_qubits: int) -> CircuitBuilder:
    # 2-qubit Grover search for |11>
    if num_qubits != 2:
        raise ValueError("Prototype Grover only supports 2 qubits")
        
    builder = simple_circuit(num_qubits, "grover_2")
    
    # Initialization
    builder.h(0)
    builder.h(1)
    
    # Oracle for |11> (CZ = H CX H)
    builder.h(1)
    builder.cx(0, 1)
    builder.h(1)
    
    # Diffuser (H, X, Z, X, H)
    builder.h(0)
    builder.h(1)
    builder.x(0)
    builder.x(1)
    
    builder.h(1)
    builder.cx(0, 1)
    builder.h(1)
    
    builder.x(0)
    builder.x(1)
    builder.h(0)
    builder.h(1)
    
    return builder
