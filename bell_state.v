Require Import QuantumLib.
Import ListNotations.

Definition bell_state_circuit : Circuit := [
  mkInstruction H_Gate [0];
  mkInstruction CNOT_Gate [0; 1]
].