# CLAUDE.md - Verified Quantum Toolkit (VQT)

## Common Commands

### Testing
- **Run All Tests**: `python -m pytest tests/ -v` (73 tests covering IR, simulator, optimization, equivalence, certificates, pipeline, QASM, noise, dashboard)
- **Run Single Test File**: `python -m pytest tests/test_simulator.py -v`

### Demos & Benchmarks
- **Run Certified Bell State Demo**: `python -m vqt.cli.main`
  - Runs full pipeline: Build -> Optimize (IdentityRemoval + GateCancellation) -> Coq (if available) -> Simulate -> Certify -> Sign.
- **Run with Noise Comparison**: `python -m vqt.cli.main --noise`
  - Appends noise model comparison showing fidelity advantage of optimized circuit.
- **Run with HTML Dashboard**: `python -m vqt.cli.main --dashboard dashboard.html`
  - Generates a self-contained HTML certificate dashboard.
- **Load from QASM File**: `python -m vqt.cli.main --qasm circuit.qasm`
  - Loads an OpenQASM 2.0 file instead of the built-in demo circuit.
- **Run Benchmarks (Grover/QFT)**: `python -m vqt.benchmarks.runner`

### Verification (Coq)
- **Run Coq Proofs**: `python -m vqt.verification.run_coq`
- **Manual Coq Compile**: `coqc -R vqt/verification VQT vqt/verification/BellProof.v`

### Dependencies
- **Required**: `pip install numpy`
- **Optional**: `pip install qiskit` (for Qiskit backend verification)

## Architecture Overview

- **`vqt/core/ir.py`**: Canonical IR (`QuantumCircuit`, `Gate`, `Qubit`, `Instruction`) + SHA-256 hashing + validation + metrics (gate_count, depth, gate_count_by_type).
- **`vqt/dsl/builder.py`**: `CircuitBuilder` DSL with 9 gates: h, x, y, z, s, t, rz, cx, swap.
- **`vqt/compiler/simulator.py`**: Trusted `NativeSimulator` — statevector simulation with full matrix construction. Supports all 9 gate types. SWAP uses CX decomposition.
- **`vqt/compiler/noise.py`**: `NoisySimulator` — density matrix simulation with depolarizing and amplitude damping channels. `NoiseConfig` dataclass. `fidelity(rho, target_state)` function.
- **`vqt/optimization/`**:
  - `optimizer.py`: Base `Optimizer` class, `ProofObject`, `OptimizationTrace` dataclasses.
  - `passes.py`: `GateCancellationPass` (adjacent self-inverse), `IdentityRemovalPass` (RZ(0), id gates), `CommuteThenCancelPass` (commute-then-cancel with conservative rules).
- **`vqt/certification/`**:
  - `equivalence.py`: `EquivalenceChecker` — fidelity-based statevector comparison.
  - `certifier.py`: `Certifier` (generates `ExecutionCertificate`), `CertificateSigner` (HMAC-SHA256 sign/verify).
- **`vqt/qasm/parser.py`**: OpenQASM 2.0 parser (`QASMParser`, `parse_qasm`, `parse_qasm_file`) and exporter (`circuit_to_qasm`). Supports all 9 VQT gates.
- **`vqt/dashboard/generator.py`**: `circuit_to_ascii` (ASCII circuit diagrams), `generate_dashboard` (self-contained HTML with SVG charts), `save_dashboard`.
- **`vqt/backends/qiskit_interface.py`**: Optional Qiskit translation (all 9 gates).
- **`vqt/verification/`**: Coq proof scaffolding — `QuantumLib.v`, `IRSemantics.v`, `OptimizationCorrectness.v`, `BellProof.v`. All use `Admitted`.
- **`vqt/benchmarks/`**: Grover (2q) and QFT (n-qubit) benchmark circuits.
- **`tests/`**: pytest suite — `test_ir.py`, `test_simulator.py`, `test_optimization.py`, `test_equivalence.py`, `test_certificate.py`, `test_pipeline.py`, `test_qasm.py`, `test_noise.py`, `test_dashboard.py`.

## Coding Standards

### Python
- **Typing**: Strict type hints required (`List`, `Dict`, `Optional`).
- **Safety**:
  - ALWAYS sanitize inputs to `Certifier` (convert numpy types to python native types).
  - Use `vqt.core.ir` objects for all internal logic.
  - `Qubit(register_name, index)` — `register_name` must be `str`, not a `QuantumRegister` object.
  - HTML dashboard uses `html.escape()` on all user-supplied strings.
  - QASM parser validates parameter expressions before `eval()`.
- **Style**:
  - Dataclasses for data structures (`OptimizationTrace`, `ProofObject`, `NoiseConfig`).
  - Hashing must be deterministic (sort dictionary keys).

### Coq
- **Status**: Scaffolding only — all proofs use `Admitted`.
- **Structure**: QuantumLib.v -> IRSemantics.v -> OptimizationCorrectness.v -> BellProof.v.
