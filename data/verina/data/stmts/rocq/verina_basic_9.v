(* Statement-only formalization of VERINA corpus artifact verina_basic_9,
   catalog title "hasCommonElement": an executable Boolean test for whether
   two nonempty integer arrays share an element, together with its correctness
   contract. This file contains no proof. *)

From Stdlib Require Import Lists.List ZArith.

Open Scope Z_scope.

Definition hasCommonElement_precond (a b : list Z) : Prop :=
  (0 < length a)%nat /\ (0 < length b)%nat.

Definition hasCommonElement
    (a b : list Z)
    (_h_precond : hasCommonElement_precond a b) : bool :=
  existsb
    (fun x => existsb (fun y => Z.eqb x y) b)
    a.

Definition hasCommonElement_postcond
    (a b : list Z)
    (result : bool)
    (_h_precond : hasCommonElement_precond a b) : Prop :=
  (exists i j : nat,
      (i < length a)%nat /\
      (j < length b)%nat /\
      nth i a 0%Z = nth j b 0%Z) <->
  result = true.

Theorem hasCommonElement_spec_satisfied
    (a b : list Z)
    (h_precond : hasCommonElement_precond a b) :
  hasCommonElement_postcond
    a b (hasCommonElement a b h_precond) h_precond.
Admitted.
