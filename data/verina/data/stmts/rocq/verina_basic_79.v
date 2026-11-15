(* Statement-only formalization of VERINA corpus artifact verina_basic_79,
   catalog title "onlineMax": an executable scan computing the maximum of the
   first x integer-array entries and the first later entry exceeding it, or
   the final array index if none does, together with its precondition,
   postcondition, and final correctness proposition. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition onlineMax_precond (a : list Z) (x : nat) : Prop :=
  (0 < length a)%nat /\
  (0 < x)%nat /\
  (x < length a)%nat.

Fixpoint findBest_fuel
    (fuel : nat)
    (a : list Z)
    (x i : nat)
    (best : Z) : Z :=
  match fuel with
  | O => best
  | S fuel' =>
      if Nat.ltb i x
      then
        let ai := nth i a 0%Z in
        let newBest := if Z.gtb ai best then ai else best in
        findBest_fuel fuel' a x (S i) newBest
      else best
  end.

Definition findBest
    (a : list Z)
    (x i : nat)
    (best : Z) : Z :=
  findBest_fuel (Nat.sub x i) a x i best.

Fixpoint findP_fuel
    (fuel : nat)
    (a : list Z)
    (x : nat)
    (m : Z)
    (i : nat) : nat :=
  match fuel with
  | O => Nat.sub (length a) 1%nat
  | S fuel' =>
      if Nat.ltb i (length a)
      then
        if Z.gtb (nth i a 0%Z) m
        then i
        else findP_fuel fuel' a x m (S i)
      else Nat.sub (length a) 1%nat
  end.

Definition findP
    (a : list Z)
    (x : nat)
    (m : Z)
    (i : nat) : nat :=
  findP_fuel (Nat.sub (length a) i) a x m i.

Definition onlineMax
    (a : list Z)
    (x : nat)
    (_h_precond : onlineMax_precond a x) : (Z * nat)%type :=
  let best := nth 0%nat a 0%Z in
  let m := findBest a x 1%nat best in
  let p := findP a x m x in
  (m, p).

Definition onlineMax_postcond
    (a : list Z)
    (x : nat)
    (result : (Z * nat)%type)
    (_h_precond : onlineMax_precond a x) : Prop :=
  let m := fst result in
  let p := snd result in
  (x <= p)%nat /\
  (p < length a)%nat /\
  (forall i : nat,
      (i < x)%nat ->
      (nth i a 0%Z <= m)%Z) /\
  (exists i : nat,
      (i < x)%nat /\
      nth i a 0%Z = m) /\
  (forall i : nat,
      (x <= i)%nat ->
      (i < p)%nat ->
      (nth i a 0%Z <= m)%Z) /\
  ((nth p a 0%Z > m)%Z \/
    (p = Nat.sub (length a) 1%nat /\
      forall i : nat,
        (x <= i)%nat ->
        (i < length a)%nat ->
        (nth i a 0%Z <= m)%Z)).

Theorem onlineMax_spec_satisfied
    (a : list Z)
    (x : nat)
    (h_precond : onlineMax_precond a x) :
  onlineMax_postcond
    a x (onlineMax a x h_precond) h_precond.
Admitted.
