(* Statement-only formalization of PutnamBench corpus artifact putnam_1989_b2:
   every nonempty left- and right-cancellative semigroup whose positive powers
   of each element form a finite set is a group; this file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Ensembles Finite_sets.

Record putnam_1989_b2_semigroup (S : Type) : Type := {
  putnam_1989_b2_mul : S -> S -> S;
  putnam_1989_b2_assoc :
    forall x y z : S,
      putnam_1989_b2_mul x (putnam_1989_b2_mul y z) =
      putnam_1989_b2_mul (putnam_1989_b2_mul x y) z
}.

Arguments putnam_1989_b2_mul {S} _ _ _.

Definition putnam_1989_b2_cancellative
    {S : Type}
    (sg : putnam_1989_b2_semigroup S) : Prop :=
  forall x y z : S,
    (putnam_1989_b2_mul sg x y =
       putnam_1989_b2_mul sg x z ->
     y = z) /\
    (putnam_1989_b2_mul sg y x =
       putnam_1989_b2_mul sg z x ->
     y = z).

Fixpoint putnam_1989_b2_positive_power
    {S : Type}
    (sg : putnam_1989_b2_semigroup S)
    (a : S)
    (n : nat) : S :=
  match n with
  | O => a
  | S k =>
      putnam_1989_b2_mul sg a
        (putnam_1989_b2_positive_power sg a k)
  end.

Definition putnam_1989_b2_finite_positive_powers
    {S : Type}
    (sg : putnam_1989_b2_semigroup S) : Prop :=
  forall a : S,
    Finite S
      (fun x : S =>
        exists n : nat,
          x = putnam_1989_b2_positive_power sg a n).

Definition putnam_1989_b2_is_group
    {S : Type}
    (sg : putnam_1989_b2_semigroup S) : Prop :=
  exists e : S,
    forall x : S,
      putnam_1989_b2_mul sg e x = x /\
      putnam_1989_b2_mul sg x e = x /\
      exists y : S,
        putnam_1989_b2_mul sg x y = e /\
        putnam_1989_b2_mul sg y x = e.

Definition putnam_1989_b2_solution : Prop := True.

Theorem putnam_1989_b2 :
  (forall (S : Type) (sg : putnam_1989_b2_semigroup S),
    (exists a : S, True) ->
    putnam_1989_b2_cancellative sg ->
    putnam_1989_b2_finite_positive_powers sg ->
    putnam_1989_b2_is_group sg) <->
  putnam_1989_b2_solution.
Admitted.
