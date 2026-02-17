from vqt.core.ir import QuantumCircuit, Gate, Qubit, Clbit

class CircuitBuilder:
    def __init__(self, name: str = "vqt_circuit"):
        self.circuit = QuantumCircuit(name)
        self.qreg = self.circuit.add_qreg("q", 0) # Dynamic sizing or fixed? Let's start with dynamic.
        self.creg = self.circuit.add_creg("c", 0)

    def qreg_size(self, size: int):
        self.qreg.size = size

    def creg_size(self, size: int):
        self.creg.size = size

    def h(self, qubit_idx: int):
        gate = Gate("h", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])

    def x(self, qubit_idx: int):
        gate = Gate("x", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])
    
    def y(self, qubit_idx: int):
        gate = Gate("y", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])

    def z(self, qubit_idx: int):
        gate = Gate("z", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])

    def s(self, qubit_idx: int):
        gate = Gate("s", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])

    def t(self, qubit_idx: int):
        gate = Gate("t", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])

    def rz(self, qubit_idx: int, theta: float):
        gate = Gate("rz", 1, [theta])
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)])

    def cx(self, control_idx: int, target_idx: int):
        gate = Gate("cx", 2)
        self.circuit.append(gate, [Qubit(self.qreg.name, control_idx), Qubit(self.qreg.name, target_idx)])
    
    def swap(self, qubit1_idx: int, qubit2_idx: int):
        gate = Gate("swap", 2)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit1_idx), Qubit(self.qreg.name, qubit2_idx)])

    def measure(self, qubit_idx: int, clbit_idx: int):
        gate = Gate("measure", 1)
        self.circuit.append(gate, [Qubit(self.qreg.name, qubit_idx)], [Clbit(self.creg.name, clbit_idx)])

    def build(self) -> QuantumCircuit:
        return self.circuit

# Simple functional interface
def simple_circuit(num_qubits: int, name: str = "simple") -> CircuitBuilder:
    builder = CircuitBuilder(name)
    builder.qreg_size(num_qubits)
    builder.creg_size(num_qubits)
    return builder
