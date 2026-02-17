from typing import List, Union, Optional, Dict, Any
from dataclasses import dataclass, field, asdict
import hashlib
import json

@dataclass
class QuantumRegister:
    name: str
    size: int

    def to_dict(self) -> Dict[str, Any]:
        return {"name": self.name, "size": self.size}

@dataclass
class ClassicalRegister:
    name: str
    size: int

    def to_dict(self) -> Dict[str, Any]:
        return {"name": self.name, "size": self.size}

@dataclass
class Qubit:
    register_name: str
    index: int

    def to_dict(self) -> Dict[str, Any]:
        return {"register": self.register_name, "index": self.index}

    def __repr__(self):
        return f"{self.register_name}[{self.index}]"

@dataclass
class Clbit:
    register_name: str
    index: int

    def to_dict(self) -> Dict[str, Any]:
        return {"register": self.register_name, "index": self.index}

    def __repr__(self):
        return f"{self.register_name}[{self.index}]"

class Gate:
    def __init__(self, name: str, num_qubits: int, params: List[float] = None):
        self.name = name
        self.num_qubits = num_qubits
        self.params = params or []

    def to_dict(self) -> Dict[str, Any]:
        return {
            "name": self.name,
            "num_qubits": self.num_qubits,
            "params": self.params
        }

    def __repr__(self):
        return f"Gate({self.name}, {self.num_qubits}, {self.params})"

@dataclass
class Instruction:
    gate: Gate
    qubits: List[Qubit]
    clbits: List[Clbit] = field(default_factory=list)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "gate": self.gate.to_dict(),
            "qubits": [q.to_dict() for q in self.qubits],
            "clbits": [c.to_dict() for c in self.clbits]
        }

    def __repr__(self):
        return f"Instruction({self.gate.name}, {self.qubits}, {self.clbits})"

class QuantumCircuit:
    def __init__(self, name: str = "vqt_circuit"):
        self.name = name
        self.qregs: List[QuantumRegister] = []
        self.cregs: List[ClassicalRegister] = []
        self.instructions: List[Instruction] = []

    def add_qreg(self, name: str, size: int) -> QuantumRegister:
        # Check for duplicate names
        if any(r.name == name for r in self.qregs):
            raise ValueError(f"QuantumRegister with name '{name}' already exists.")
        qreg = QuantumRegister(name, size)
        self.qregs.append(qreg)
        return qreg

    def add_creg(self, name: str, size: int) -> ClassicalRegister:
        if any(r.name == name for r in self.cregs):
            raise ValueError(f"ClassicalRegister with name '{name}' already exists.")
        creg = ClassicalRegister(name, size)
        self.cregs.append(creg)
        return creg

    def _find_qreg(self, name: str) -> Optional[QuantumRegister]:
        for r in self.qregs:
            if r.name == name:
                return r
        return None

    def _find_creg(self, name: str) -> Optional[ClassicalRegister]:
        for r in self.cregs:
            if r.name == name:
                return r
        return None

    def append(self, gate: Gate, qubits: List[Qubit], clbits: List[Clbit] = None):
        # Validate gate arity
        if gate.num_qubits != len(qubits):
            raise ValueError(
                f"Gate '{gate.name}' expects {gate.num_qubits} qubits, got {len(qubits)}"
            )
        # Validate qubit registers and indices
        for q in qubits:
            reg = self._find_qreg(q.register_name)
            if reg is None:
                raise ValueError(f"Quantum register '{q.register_name}' not found")
            if q.index < 0 or q.index >= reg.size:
                raise IndexError(
                    f"Qubit index {q.index} out of bounds for register "
                    f"'{q.register_name}' (size {reg.size})"
                )
        # Validate classical bits
        for c in (clbits or []):
            reg = self._find_creg(c.register_name)
            if reg is None:
                raise ValueError(f"Classical register '{c.register_name}' not found")
            if c.index < 0 or c.index >= reg.size:
                raise IndexError(
                    f"Clbit index {c.index} out of bounds for register "
                    f"'{c.register_name}' (size {reg.size})"
                )
        instruction = Instruction(gate, qubits, clbits or [])
        self.instructions.append(instruction)

    @property
    def num_qubits(self) -> int:
        return sum(r.size for r in self.qregs)

    @property
    def num_clbits(self) -> int:
        return sum(r.size for r in self.cregs)

    @property
    def gate_count(self) -> int:
        return len(self.instructions)

    def gate_count_by_type(self) -> Dict[str, int]:
        counts: Dict[str, int] = {}
        for instr in self.instructions:
            name = instr.gate.name
            counts[name] = counts.get(name, 0) + 1
        return counts

    @property
    def depth(self) -> int:
        if not self.instructions:
            return 0
        n = self.num_qubits
        qubit_time = [0] * n
        for instr in self.instructions:
            indices = [q.index for q in instr.qubits]
            start = max(qubit_time[i] for i in indices)
            for i in indices:
                qubit_time[i] = start + 1
        return max(qubit_time)

    def to_dict(self) -> Dict[str, Any]:
        """Returns a canonical dictionary representation."""
        return {
            "name": self.name,
            "qregs": [r.to_dict() for r in self.qregs],
            "cregs": [r.to_dict() for r in self.cregs],
            "instructions": [i.to_dict() for i in self.instructions]
        }

    def to_json(self) -> str:
        """Returns a deterministic JSON string."""
        return json.dumps(self.to_dict(), sort_keys=True, separators=(',', ':'))

    def digest(self) -> str:
        """Returns the SHA-256 hash of the canonical JSON representation."""
        canonical_json = self.to_json()
        return hashlib.sha256(canonical_json.encode('utf-8')).hexdigest()

    def __repr__(self):
        return f"QuantumCircuit({self.name}, hash={self.digest()[:8]}...)"
