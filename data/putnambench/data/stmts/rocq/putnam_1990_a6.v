(* Statement-only formalization of PutnamBench corpus artifact putnam_1990_a6:
   the number of admissible ordered pairs of subsets of {1,...,10}, under the
   prescribed cross-cardinality inequalities, is 17711. This file contains no
   proof. *)

From mathcomp Require Import all_ssreflect.

Definition putnam_1990_a6_admissible
    (ST : {set 'I_10} * {set 'I_10}) : bool :=
  let '(xs, ys) := ST in
  [forall s : 'I_10, (s \in xs) ==> (#|ys| < s.+1)] &&
  [forall t : 'I_10, (t \in ys) ==> (#|xs| < t.+1)].

Definition putnam_1990_a6_admissible_pairs :=
  [set ST : {set 'I_10} * {set 'I_10} |
    putnam_1990_a6_admissible ST].

Definition putnam_1990_a6_solution : nat := 17711.

Theorem putnam_1990_a6 :
  #|putnam_1990_a6_admissible_pairs| = putnam_1990_a6_solution.
Admitted.
