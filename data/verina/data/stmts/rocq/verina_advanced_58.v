(* Statement-only formalization of VERINA corpus artifact verina_advanced_58,
   catalog title "nthUglyNumber": an executable three-pointer generation of
   the nth positive integer whose only prime factors are 2, 3, and 5, together
   with its factor-stripping correctness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition nthUglyNumber_precond (n : nat) : Prop :=
  (0 < n)%nat.

Definition nextUgly
    (values : list nat)
    (c2 c3 c5 : nat) : nat * nat * nat * nat :=
  let i2 := nth c2 values 0 * 2 in
  let i3 := nth c3 values 0 * 3 in
  let i5 := nth c5 values 0 * 5 in
  let next := Nat.min i2 (Nat.min i3 i5) in
  let c2' := if Nat.eqb next i2 then S c2 else c2 in
  let c3' := if Nat.eqb next i3 then S c3 else c3 in
  let c5' := if Nat.eqb next i5 then S c5 else c5 in
  (next, c2', c3', c5').

Fixpoint nthUglyNumber_loop
    (i : nat)
    (values : list nat)
    (c2 c3 c5 : nat)
    {struct i} : list nat :=
  match i with
  | 0 => values
  | S i' =>
      let '(next, c2', c3', c5') :=
        nextUgly values c2 c3 c5 in
      nthUglyNumber_loop
        i' (values ++ [next]) c2' c3' c5'
  end.

Definition nthUglyNumber
    (n : nat)
    (_h_precond : nthUglyNumber_precond n) : nat :=
  let index := n - 1 in
  nth index
    (nthUglyNumber_loop index [1] 0 0 0)
    0.

Fixpoint divideOut_fuel
    (fuel n p : nat)
    {struct fuel} : nat :=
  match fuel with
  | 0 => n
  | S fuel' =>
      if andb
           (Nat.ltb 1 p)
           (andb
             (Nat.ltb 0 n)
             (Nat.eqb (Nat.modulo n p) 0))
      then divideOut_fuel fuel' (Nat.div n p) p
      else n
  end.

Definition divideOut (n p : nat) : nat :=
  divideOut_fuel n n p.

Definition isUgly (x : nat) : bool :=
  if Nat.eqb x 0
  then false
  else
    let n1 := divideOut x 2 in
    let n2 := divideOut n1 3 in
    let n3 := divideOut n2 5 in
    Nat.eqb n3 1.

Definition nthUglyNumber_postcond
    (n result : nat)
    (_h_precond : nthUglyNumber_precond n) : Prop :=
  isUgly result = true /\
  length (filter isUgly (seq 0 result)) = n - 1.

Theorem nthUglyNumber_spec_satisfied
    (n : nat)
    (h_precond : nthUglyNumber_precond n) :
  nthUglyNumber_postcond
    n (nthUglyNumber n h_precond) h_precond.
Admitted.
