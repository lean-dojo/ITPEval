(*
  Statement-only formalization of Thousand Theorems corpus artifact Q810431
  (thousand-theorems__rocq__Q810431), "Basel problem": the
  natural-number-indexed real reciprocal-square series sums to pi squared
  divided by six. This file contains no proof.
*)

From Stdlib Require Import Reals SeqSeries.

Local Open Scope R_scope.

Theorem hasSum_zeta_two :
  infinite_sum
    (fun n : nat => 1 / (INR n) ^ 2)
    (PI ^ 2 / 6).
Admitted.
