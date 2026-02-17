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

    def append(self, gate: Gate, qubits: List[Qubit], clbits: List[Clbit] = None):
        instruction = Instruction(gate, qubits, clbits or [])
        self.instructions.append(instruction)

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
