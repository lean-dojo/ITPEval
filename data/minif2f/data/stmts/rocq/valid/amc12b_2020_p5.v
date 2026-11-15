Require Import Nat.

Theorem amc12b_2020_p5 :
  forall (ap bp aw al bw bl : nat),
  ap = aw + al -> (* no draws *)
  bp = bw + bl ->
  3* aw = 2 * ap ->
  8* bw = 5 * bp ->
  (* Team B has seven more wins and seven more losses than team A. *)
  bw = aw + 7 ->
  bl = al + 7 ->
  ap = 42.
Proof.
Admitted.
