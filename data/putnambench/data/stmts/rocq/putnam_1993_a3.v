(* Statement-only formalization of PutnamBench corpus artifact putnam_1993_a3:
   counting intersection-preserving maps from the subsets of an n-element set
   to an m-element chain. This file contains no proof. *)

From mathcomp Require Import all_ssreflect.

Definition putnam_1993_a3_admissible {n m : nat}
    (f : {ffun {set 'I_n} -> 'I_m}) : bool :=
  [forall A : {set 'I_n},
    [forall B : {set 'I_n},
      nat_of_ord (f (A :&: B)) ==
      minn (nat_of_ord (f A)) (nat_of_ord (f B))]].

Theorem putnam_1993_a3 :
  forall n m : nat,
    (1 <= n)%nat ->
    (1 <= m)%nat ->
    #|[pred f : {ffun {set 'I_n} -> 'I_m} |
        putnam_1993_a3_admissible f]| =
    \sum_(1 <= j < m.+1) j ^ n.
Admitted.
