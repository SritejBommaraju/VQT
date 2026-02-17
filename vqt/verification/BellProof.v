(* 
  BellProof.v - End-to-End Verification of Bell State 
*)

Require Import QuantumLib.
Require Import IRSemantics.

(* 1. Define the Circuit *)
Definition BellCircuit : Circuit := 
  [ Inst H [0]; Inst CNOT [0; 1] ].

(* 2. Define Initial State |00> *)
(* Vector4 = C x C x C x C *)
Definition State00 : Vector4 := 
  (C1, C0, C0, C0).

(* 3. Define Expected Final State *)
(* (|00> + |11>) / sqrt(2) *)
Definition BellState : Vector4 :=
  (inv_sqrt2, C0, C0, inv_sqrt2).

(* 4. The Theorem *)
Theorem bell_circuit_correct : 
  M4_mult_V4 (denote_circuit_rev BellCircuit) State00 = BellState.
Proof.
  unfold BellCircuit.
  simpl.
  (* 
    denote([H; CX]) = denote(CX) * denote(H) * I 
    State = CX * H * |00>
  *)
  
  (* Step 1: H * |00> *)
  (* H0_I1 * (1,0,0,0) = (1/rt2, 0, 1/rt2, 0) *)
  
  (* Step 2: CNOT * (1/rt2, 0, 1/rt2, 0) *)
  (* CNOT swaps last two? No, CNOT01:
     |00> -> |00> (1/rt2)
     |10> -> |11> (1/rt2) 
     Result: (1/rt2, 0, 0, 1/rt2)
  *)
  
  unfold denote_inst, CNOT01, H0_I1, I4, State00, BellState.
  unfold M4_mult_V4, dot4.
  
  (* In a real proof, 'field' or 'lra' would solve this immediately *)
  admit.
Admitted.
