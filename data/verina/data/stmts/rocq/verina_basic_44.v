(* Statement-only formalization of VERINA corpus artifact verina_basic_44,
   catalog title "isOddAtIndexOdd": an executable Boolean check that every
   odd array index contains an odd integer, together with its trivial
   precondition, exact postcondition, and final correctness proposition.
   This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition isOdd (n : Z) : bool :=
  Z.eqb (Z.modulo n 2%Z) 1%Z.

Definition isOddAtIndexOdd_precond (_a : list Z) : Prop :=
  True.

Fixpoint isOddAtIndexOdd_mapIdxFrom
    (a : list Z)
    (i : nat) : list (nat * Z) :=
  match a with
  | [] => []
  | x :: xs => (i, x) :: isOddAtIndexOdd_mapIdxFrom xs (S i)
  end.

Definition isOddAtIndexOdd_mapIdx
    (a : list Z) : list (nat * Z) :=
  isOddAtIndexOdd_mapIdxFrom a 0%nat.

Definition isOddAtIndexOdd
    (a : list Z)
    (_h_precond : isOddAtIndexOdd_precond a) : bool :=
  forallb
    (fun indexed =>
      let '(i, x) := indexed in
      orb (negb (isOdd (Z.of_nat i))) (isOdd x))
    (isOddAtIndexOdd_mapIdx a).

Definition isOddAtIndexOdd_postcond
    (a : list Z)
    (result : bool)
    (_h_precond : isOddAtIndexOdd_precond a) : Prop :=
  result = true <->
  forall i : nat,
    (i < length a)%nat ->
    isOdd (Z.of_nat i) = true ->
    isOdd (nth i a 0%Z) = true.

Theorem isOddAtIndexOdd_spec_satisfied
    (a : list Z)
    (h_precond : isOddAtIndexOdd_precond a) :
  isOddAtIndexOdd_postcond
    a (isOddAtIndexOdd a h_precond) h_precond.
Admitted.
