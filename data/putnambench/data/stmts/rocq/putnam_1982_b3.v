(* Statement-only formalization of PutnamBench artifact putnam_1982_b3:
   the probability that two independent uniform choices from 1 through n
   have perfect-square sum, multiplied by sqrt(n), converges to
   (4/3) * (sqrt(2) - 1). This file contains no proof. *)

From Stdlib Require Import Reals List ClassicalDescription SeqSeries.

Open Scope R_scope.

Definition putnam_1982_b3_perfect_squareb (k : nat) : bool :=
  if excluded_middle_informative
       (exists m : nat, (m ^ 2 = k)%nat)
  then true
  else false.

Definition putnam_1982_b3_pairs (n : nat) : list (nat * nat) :=
  flat_map
    (fun c : nat => map (fun d : nat => (c, d)) (seq 1 n))
    (seq 1 n).

Definition putnam_1982_b3_pair_count (n : nat) : nat :=
  length
    (filter
      (fun pair : nat * nat =>
        putnam_1982_b3_perfect_squareb
          ((fst pair + snd pair)%nat))
      (putnam_1982_b3_pairs n)).

Definition putnam_1982_b3_solution : R :=
  (4 / 3) * (sqrt 2 - 1).

Theorem putnam_1982_b3
    (p : nat -> R)
    (hp : p =
      fun n : nat =>
        INR (putnam_1982_b3_pair_count n) / INR (n ^ 2)) :
  Un_cv
    (fun n : nat => p n * sqrt (INR n))
    putnam_1982_b3_solution.
Admitted.
