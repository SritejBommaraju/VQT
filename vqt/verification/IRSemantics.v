(* 
  IRSemantics.v - Semantics of VQT IR Instructions 
*)

Require Import QuantumLib.
Require Import List.
Import ListNotations.

(* Minimal IR Subset for Bell State + Optimization *)
Inductive Gate : Type :=
  | H | X | CNOT | Other.

Inductive Instruction : Type :=
  | Inst : Gate -> list nat -> Instruction.

Definition Circuit := list Instruction.

(* 
  Denotational Semantics
  We map instructions to 4x4 matrices (assuming 2-qubit system).
  If qubits don't match our 2-qubit model, we return Identity (simplification for prototype).
*)

Definition denote_inst (i : Instruction) : Matrix4 :=
  match i with
  | Inst H [0] => H0_I1
  | Inst X [0] => X0_I1
  | Inst CNOT [0; 1] => CNOT01
  (* For prototype, we only support exactly these for the proof.
     Real system would generate tensor products dynamically. *)
  | _ => I4 
  end.

Fixpoint denote_circuit (c : Circuit) : Matrix4 :=
  match c with
  | [] => I4
  | i :: rest => M4_mult (denote_inst i) (denote_circuit rest) 
  (* Note: Matrix multiplication order depends on convention. 
     If state is column vector |psi>, and circuit is G2 G1 |psi>, 
     then denote(G1::G2) = denote(G2) * denote(G1).
     Let's assume the list is [G1, G2]. 
     Apply G1 first, then G2. 
     So result = G2 * (G1 * I).
     Recursive: denote(i :: rest) = denote(rest) * denote(i).
  *)
  end.

(* 
  Actually, let's fix the order.
  If c = [G1; G2], we want U = G2 * G1.
  denote(G1 :: G2) 
  = denote(G2) * denote(G1)
*)
Fixpoint denote_circuit_rev (c : Circuit) : Matrix4 :=
  match c with
  | [] => I4
  | i :: rest => M4_mult (denote_circuit_rev rest) (denote_inst i)
  end.
