(* Statement-only formalization of VERINA corpus artifact verina_basic_10,
   catalog title "isGreater": an executable Boolean test for whether an
   integer is strictly greater than every element of a nonempty integer
   array, together with its correctness contract. This file contains no
   proof. *)

From Stdlib Require Import List ZArith.

Open Scope Z_scope.

Definition isGreater_precond (_n : Z) (a : list Z) : Prop :=
  (0 < length a)%nat.

Definition isGreater
    (n : Z)
    (a : list Z)
    (_h_precond : isGreater_precond n a) : bool :=
  forallb (fun x => Z.ltb x n) a.

Definition isGreater_postcond
    (n : Z)
    (a : list Z)
    (result : bool)
    (_h_precond : isGreater_precond n a) : Prop :=
  (forall (i : nat),
      (i < length a)%nat ->
      n > nth i a 0) <->
  result = true.

Theorem isGreater_spec_satisfied
    (n : Z)
    (a : list Z)
    (h_precond : isGreater_precond n a) :
  isGreater_postcond n a (isGreater n a h_precond) h_precond.
Admitted.
