(* Statement-only formalization of PutnamBench artifact putnam_1980_b4:
   a family of 1066 strict-majority subsets of a finite set with at least
   10 elements has a 10-element hitting subset. This file contains no proof. *)

From Stdlib Require Import Vectors.Fin Ensembles Finite_sets Arith.PeanoNat.

Theorem putnam_1980_b4 :
  forall
    (T : Type)
    (X : Ensemble T)
    (A : Fin.t 1066 -> Ensemble T),
    (exists nX : nat,
      cardinal T X nX /\
      (10 <= nX)%nat /\
      forall i : Fin.t 1066,
        Included T (A i) X /\
        exists nA : nat,
          cardinal T (A i) nA /\
          (nX < 2 * nA)%nat) ->
    exists Y : Ensemble T,
      Included T Y X /\
      cardinal T Y 10 /\
      forall i : Fin.t 1066,
        exists y : T,
          In T Y y /\ In T (A i) y.
Admitted.
