(* 
  QuantumLib.v - Minimal Quantum Semantics for VQT 
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Psatz.
Require Import Coq.Init.Nat.

Open Scope R_scope.

(* --- 1. Complex Numbers --- *)
(* Represent C as (Re, Im) *)
Definition C := (R * R)%type.

Definition C0 : C := (0, 0).
Definition C1 : C := (1, 0).

(* Addition *)
Definition Cplus (c1 c2 : C) : C :=
  (fst c1 + fst c2, snd c1 + snd c2).

(* Multiplication *)
Definition Cmult (c1 c2 : C) : C :=
  (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).

(* Norm squared *)
Definition Cnorm2 (c : C) : R :=
  (fst c) * (fst c) + (snd c) * (snd c).

(* Notation *)
Infix "+" := Cplus : C_scope.
Infix "*" := Cmult : C_scope.
Bind Scope C_scope with C.

(* --- 2. Vectors and Matrices (Fixed dim 4 for 2 qubits) --- *)
(* We stick to 2 qubits (dim 4) to keep it concrete and compilable without high overhead *)

Definition Vector4 := C * C * C * C.

Definition Matrix4 := Vector4 * Vector4 * Vector4 * Vector4. (* 4 rows *)

(* Matrix-Vector Multiplication *)
(* Helper: dot product of row (Vector4) and col (Vector4) *)
Definition dot4 (r : Vector4) (c : Vector4) : C :=
  let '(r1, r2, r3, r4) := r in
  let '(c1, c2, c3, c4) := c in
  (r1 * c1) + (r2 * c2) + (r3 * c3) + (r4 * c4).

(* Mat * Vec *)
Definition M4_mult_V4 (m : Matrix4) (v : Vector4) : Vector4 :=
  let '(row1, row2, row3, row4) := m in
  (dot4 row1 v, dot4 row2 v, dot4 row3 v, dot4 row4 v).

(* Identity Matrix *)
Definition I4 : Matrix4 :=
  ((C1, C0, C0, C0),
   (C0, C1, C0, C0),
   (C0, C0, C1, C0),
   (C0, C0, C0, C1)).

(* Matrix Multiplication *)
(* M1 * M2 - Requires columns of M2. For simplicity, we define M * M via rows/dots if needed, 
   but for circuit eval, we mainly need M * V. 
   Actually, for optimization (G * G = I), we need Matrix * Matrix.
*)
(* Transpose to get cols *)
Definition transpose4 (m : Matrix4) : Matrix4 :=
  let '( (a1, a2, a3, a4),
         (b1, b2, b3, b4),
         (c1, c2, c3, c4),
         (d1, d2, d3, d4) ) := m in
  ( (a1, b1, c1, d1),
    (a2, b2, c2, d2),
    (a3, b3, c3, d3),
    (a4, b4, c4, d4) ).

Definition M4_mult (m1 m2 : Matrix4) : Matrix4 :=
  let '(r1, r2, r3, r4) := m1 in
  let m2t := transpose4 m2 in
  let '(c1, c2, c3, c4) := m2t in
  ( (dot4 r1 c1, dot4 r1 c2, dot4 r1 c3, dot4 r1 c4),
    (dot4 r2 c1, dot4 r2 c2, dot4 r2 c3, dot4 r2 c4),
    (dot4 r3 c1, dot4 r3 c2, dot4 r3 c3, dot4 r3 c4),
    (dot4 r4 c1, dot4 r4 c2, dot4 r4 c3, dot4 r4 c4) ).

(* --- 3. Quantum Gates (2-Qubit System) --- *)
(* Basis: |00>, |01>, |10>, |11> *)

(* 1/sqrt(2) *)
Axiom sqrt2_inv : R.
Definition inv_sqrt2 : C := (sqrt2_inv, 0).

(* H on Qubit 0 (H x I) *)
(* H = [[1, 1], [1, -1]] * s 
   I = [[1, 0], [0, 1]]
   H x I = 
   [[s, 0, s, 0],
    [0, s, 0, s],
    [s, 0, -s, 0],
    [0, s, 0, -s]]
*)
Definition H0_I1 : Matrix4 :=
  ( (inv_sqrt2, C0, inv_sqrt2, C0),
    (C0, inv_sqrt2, C0, inv_sqrt2),
    (inv_sqrt2, C0, ((-1 * fst inv_sqrt2)%R, 0), C0),
    (C0, inv_sqrt2, C0, ((-1 * fst inv_sqrt2)%R, 0)) ).

(* CNOT 0->1 *)
(* |00> -> |00>, |01> -> |01>, |10> -> |11>, |11> -> |10> 
   Swap last two rows (indices 2 and 3, 0-based)
*)
Definition CNOT01 : Matrix4 :=
  ( (C1, C0, C0, C0),
    (C0, C1, C0, C0),
    (C0, C0, C0, C1), (* |10> maps to |11> *)
    (C0, C0, C1, C0)  (* |11> maps to |10> *)
).

(* X on Qubit 0 (X x I) *)
(* X = [[0, 1], [1, 0]]
   X x I = 
   [[0, 0, 1, 0],
    [0, 0, 0, 1],
    [1, 0, 0, 0],
    [0, 1, 0, 0]]
*)
Definition X0_I1 : Matrix4 :=
  ( (C0, C0, C1, C0),
    (C0, C0, C0, C1),
    (C1, C0, C0, C0),
    (C0, C1, C0, C0) ).

(* Equality on Matrix4 *)
Definition vec_eq (v1 v2 : Vector4) : Prop :=
  v1 = v2.

Definition mat_eq (m1 m2 : Matrix4) : Prop :=
  m1 = m2.
