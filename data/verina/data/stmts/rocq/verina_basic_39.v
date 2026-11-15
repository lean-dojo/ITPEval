(* Statement-only formalization of VERINA corpus artifact verina_basic_39,
   catalog title "rotateRight": an executable cyclic right rotation of an
   integer list by an arbitrary natural offset using integer modulo indexing,
   together with its length and pointwise correctness contract and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.

Definition rotateRight_precond
    (_l : list Z) (_n : nat) : Prop :=
  True.

Definition rotateRight_headD
    (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | x :: _ => x
  end.

Definition rotateRight_getD
    (l : list Z) (index : nat) (default : Z) : Z :=
  nth index l default.

Definition rotateRight_index
    (i n len : nat) : nat :=
  Z.to_nat
    (Z.modulo
      (Z.of_nat i - Z.of_nat n + Z.of_nat len)
      (Z.of_nat len)).

Definition rotateRight
    (l : list Z)
    (n : nat)
    (_h_precond : rotateRight_precond l n) : list Z :=
  let len := length l in
  match len with
  | O => l
  | S _ =>
      map
        (fun i =>
          rotateRight_getD
            l
            (rotateRight_index i n len)
            (rotateRight_headD l 0%Z))
        (seq 0%nat len)
  end.

Definition rotateRight_postcond
    (l : list Z)
    (n : nat)
    (result : list Z)
    (_h_precond : rotateRight_precond l n) : Prop :=
  length result = length l /\
  forall i : nat,
    (i < length l)%nat ->
    nth_error result i =
      nth_error l (rotateRight_index i n (length l)).

Theorem rotateRight_spec_satisfied
    (l : list Z)
    (n : nat)
    (h_precond : rotateRight_precond l n) :
  rotateRight_postcond
    l n (rotateRight l n h_precond) h_precond.
Admitted.
