(* Statement-only formalization of VERINA corpus artifact verina_basic_56,
   catalog title "copy": executable copying of a bounded segment from a source
   integer array into a destination integer array, together with its
   precondition, postcondition, and final correctness proposition. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition copy_precond
    (src : list Z)
    (sStart : nat)
    (dest : list Z)
    (dStart len : nat) : Prop :=
  (sStart + len <= length src)%nat /\
  (dStart + len <= length dest)%nat.

Fixpoint copy_set_nth
    (index : nat)
    (value : Z)
    (xs : list Z) : list Z :=
  match xs with
  | [] => []
  | x :: rest =>
      match index with
      | O => value :: rest
      | S index' => x :: copy_set_nth index' value rest
      end
  end.

Fixpoint updateSegment
    (r src : list Z)
    (sStart dStart n : nat) : list Z :=
  match n with
  | O => r
  | S n' =>
      let rNew :=
        copy_set_nth
          (dStart + n')%nat
          (nth (sStart + n')%nat src 0%Z)
          r in
      updateSegment rNew src sStart dStart n'
  end.

Definition copy
    (src : list Z)
    (sStart : nat)
    (dest : list Z)
    (dStart len : nat)
    (_h_precond : copy_precond src sStart dest dStart len) : list Z :=
  if Nat.eqb len O
  then dest
  else updateSegment dest src sStart dStart len.

Definition copy_postcond
    (src : list Z)
    (sStart : nat)
    (dest : list Z)
    (dStart len : nat)
    (result : list Z)
    (_h_precond : copy_precond src sStart dest dStart len) : Prop :=
  length result = length dest /\
  (forall i : nat,
      (i < dStart)%nat ->
      nth i result 0%Z = nth i dest 0%Z) /\
  (forall i : nat,
      (dStart + len <= i)%nat ->
      (i < length result)%nat ->
      nth i result 0%Z = nth i dest 0%Z) /\
  (forall i : nat,
      (i < len)%nat ->
      nth (dStart + i)%nat result 0%Z =
      nth (sStart + i)%nat src 0%Z).

Theorem copy_spec_satisfied
    (src : list Z)
    (sStart : nat)
    (dest : list Z)
    (dStart len : nat)
    (h_precond : copy_precond src sStart dest dStart len) :
  copy_postcond
    src sStart dest dStart len
    (copy src sStart dest dStart len h_precond)
    h_precond.
Admitted.
