"""OpenQASM 2.0 parser and exporter for VQT circuits."""

import re
import math
from typing import List, Tuple, Optional, Dict, Any
from vqt.core.ir import QuantumCircuit, Gate, Qubit, Clbit


class QASMParseError(Exception):
    """Raised when QASM parsing fails."""
    pass


class QASMParser:
    """Parse OpenQASM 2.0 strings into VQT QuantumCircuit objects."""

    # Maps QASM gate name -> (VQT name, num_qubits, has_params)
    GATE_MAP: Dict[str, Tuple[str, int, bool]] = {
        'h': ('h', 1, False),
        'x': ('x', 1, False),
        'y': ('y', 1, False),
        'z': ('z', 1, False),
        's': ('s', 1, False),
        't': ('t', 1, False),
        'rz': ('rz', 1, True),
        'cx': ('cx', 2, False),
        'swap': ('swap', 2, False),
    }

    def parse(self, qasm_str: str, circuit_name: str = "qasm_circuit") -> QuantumCircuit:
        """Parse an OpenQASM 2.0 string into a QuantumCircuit."""
        circuit = QuantumCircuit(circuit_name)
        lines = qasm_str.strip().split('\n')
        version_found = False

        for line_num, raw_line in enumerate(lines, 1):
            # Strip comments
            line = re.sub(r'//.*$', '', raw_line).strip()
            if not line or line == '':
                continue

            # Version declaration
            if line.startswith('OPENQASM'):
                match = re.match(r'OPENQASM\s+([\d.]+)\s*;', line)
                if not match:
                    raise QASMParseError(f"Line {line_num}: Invalid OPENQASM declaration")
                version = match.group(1)
                if version != '2.0':
                    raise QASMParseError(
                        f"Line {line_num}: Unsupported QASM version '{version}', only 2.0 is supported"
                    )
                version_found = True
                continue

            # Include statement (ignored)
            if line.startswith('include'):
                continue

            # Quantum register declaration
            qreg_match = re.match(r'qreg\s+(\w+)\s*\[\s*(\d+)\s*\]\s*;', line)
            if qreg_match:
                name = qreg_match.group(1)
                size = int(qreg_match.group(2))
                circuit.add_qreg(name, size)
                continue

            # Classical register declaration
            creg_match = re.match(r'creg\s+(\w+)\s*\[\s*(\d+)\s*\]\s*;', line)
            if creg_match:
                name = creg_match.group(1)
                size = int(creg_match.group(2))
                circuit.add_creg(name, size)
                continue

            # Measure statement: measure q[0] -> c[0];
            measure_match = re.match(
                r'measure\s+(\w+)\s*\[\s*(\d+)\s*\]\s*->\s*(\w+)\s*\[\s*(\d+)\s*\]\s*;', line
            )
            if measure_match:
                qreg_name = measure_match.group(1)
                q_idx = int(measure_match.group(2))
                creg_name = measure_match.group(3)
                c_idx = int(measure_match.group(4))
                gate = Gate("measure", 1)
                circuit.append(gate, [Qubit(qreg_name, q_idx)], [Clbit(creg_name, c_idx)])
                continue

            # Barrier (ignored)
            if line.startswith('barrier'):
                continue

            # Gate application with parameters: rz(pi/4) q[0];
            gate_param_match = re.match(
                r'(\w+)\s*\(([^)]*)\)\s+(.+);', line
            )
            if gate_param_match:
                gate_name = gate_param_match.group(1).lower()
                param_str = gate_param_match.group(2).strip()
                qubit_str = gate_param_match.group(3).strip()

                if gate_name not in self.GATE_MAP:
                    raise QASMParseError(f"Line {line_num}: Unknown gate '{gate_name}'")

                vqt_name, num_qubits, has_params = self.GATE_MAP[gate_name]
                params = [self._eval_param(param_str)] if has_params else []
                qubits = self._parse_qubit_refs(qubit_str)

                if len(qubits) != num_qubits:
                    raise QASMParseError(
                        f"Line {line_num}: Gate '{gate_name}' expects {num_qubits} qubits, got {len(qubits)}"
                    )

                gate = Gate(vqt_name, num_qubits, params)
                circuit.append(gate, qubits)
                continue

            # Gate application without parameters: h q[0]; cx q[0], q[1];
            gate_match = re.match(r'(\w+)\s+(.+);', line)
            if gate_match:
                gate_name = gate_match.group(1).lower()
                qubit_str = gate_match.group(2).strip()

                if gate_name not in self.GATE_MAP:
                    raise QASMParseError(f"Line {line_num}: Unknown gate '{gate_name}'")

                vqt_name, num_qubits, has_params = self.GATE_MAP[gate_name]
                qubits = self._parse_qubit_refs(qubit_str)

                if len(qubits) != num_qubits:
                    raise QASMParseError(
                        f"Line {line_num}: Gate '{gate_name}' expects {num_qubits} qubits, got {len(qubits)}"
                    )

                gate = Gate(vqt_name, num_qubits)
                circuit.append(gate, qubits)
                continue

            # If nothing matched and line isn't empty, raise error
            raise QASMParseError(f"Line {line_num}: Unrecognized statement: '{line}'")

        return circuit

    def _eval_param(self, expr: str) -> float:
        """Safely evaluate a parameter expression like 'pi/4' or '3.14'."""
        expr = expr.strip()
        # Replace 'pi' with math.pi value
        safe_expr = expr.replace('pi', str(math.pi))
        # Validate: only allow digits, '.', '+', '-', '*', '/', '(', ')', spaces
        if not re.match(r'^[\d.+\-*/() e]+$', safe_expr):
            raise QASMParseError(f"Unsafe parameter expression: '{expr}'")
        try:
            return float(eval(safe_expr))
        except Exception as e:
            raise QASMParseError(f"Cannot evaluate parameter '{expr}': {e}")

    def _parse_qubit_refs(self, s: str) -> List[Qubit]:
        """Parse qubit references like 'q[0], q[1]' into Qubit objects."""
        refs = []
        parts = [p.strip() for p in s.split(',')]
        for part in parts:
            match = re.match(r'(\w+)\s*\[\s*(\d+)\s*\]', part)
            if not match:
                raise QASMParseError(f"Invalid qubit reference: '{part}'")
            reg_name = match.group(1)
            idx = int(match.group(2))
            refs.append(Qubit(reg_name, idx))
        return refs


def parse_qasm(qasm_str: str, name: str = "qasm_circuit") -> QuantumCircuit:
    """Convenience function to parse a QASM string."""
    return QASMParser().parse(qasm_str, name)


def parse_qasm_file(filepath: str, name: Optional[str] = None) -> QuantumCircuit:
    """Parse a QASM file into a QuantumCircuit."""
    if name is None:
        name = filepath.rsplit('/', 1)[-1].rsplit('\\', 1)[-1].replace('.qasm', '')
    with open(filepath, 'r') as f:
        return parse_qasm(f.read(), name)


def circuit_to_qasm(circuit: QuantumCircuit) -> str:
    """Export a VQT QuantumCircuit to an OpenQASM 2.0 string."""
    lines = [
        'OPENQASM 2.0;',
        'include "qelib1.inc";',
    ]

    # Register declarations
    for qreg in circuit.qregs:
        lines.append(f'qreg {qreg.name}[{qreg.size}];')
    for creg in circuit.cregs:
        lines.append(f'creg {creg.name}[{creg.size}];')

    # Instructions
    for instr in circuit.instructions:
        gate_name = instr.gate.name.lower()
        qubit_strs = [f'{q.register_name}[{q.index}]' for q in instr.qubits]

        if gate_name == 'measure':
            clbit_strs = [f'{c.register_name}[{c.index}]' for c in instr.clbits]
            lines.append(f'measure {qubit_strs[0]} -> {clbit_strs[0]};')
        elif instr.gate.params:
            param_str = ', '.join(_format_param(p) for p in instr.gate.params)
            lines.append(f'{gate_name}({param_str}) {", ".join(qubit_strs)};')
        else:
            lines.append(f'{gate_name} {", ".join(qubit_strs)};')

    return '\n'.join(lines) + '\n'


def _format_param(value: float) -> str:
    """Format a parameter value, using pi fractions where possible."""
    if value == 0.0:
        return '0'
    ratio = value / math.pi
    # Check common fractions
    for denom in [1, 2, 4, 8]:
        numer = round(ratio * denom)
        if abs(numer / denom - ratio) < 1e-10:
            if denom == 1:
                if numer == 1:
                    return 'pi'
                elif numer == -1:
                    return '-pi'
                return f'{numer}*pi'
            if numer == 1:
                return f'pi/{denom}'
            if numer == -1:
                return f'-pi/{denom}'
            return f'{numer}*pi/{denom}'
    return str(value)
