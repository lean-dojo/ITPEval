(*
  Statement-only formalization of Logipedia corpus artifact nat.nat_ind
  (catalog title "nat.nat_ind"): mathematical induction for arbitrary
  predicates on natural numbers from the zero and successor cases. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_nat_ind :
  forall Q : nat -> Prop,
    Q O ->
    (forall x : nat, Q x -> Q (S x)) ->
    forall x : nat, Q x.
Admitted.
