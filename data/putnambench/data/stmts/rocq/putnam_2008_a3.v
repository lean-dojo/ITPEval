(* Statement-only formalization of PutnamBench corpus artifact putnam_2008_a3:
   repeated gcd-lcm replacements on a finite sequence of positive integers
   terminate at a sequence independent of the choices; this file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat Vectors.Fin.

Definition putnam_2008_a3_index_lt
    {n : nat} (i j : Fin.t n) : Prop :=
  (proj1_sig (Fin.to_nat i) < proj1_sig (Fin.to_nat j))%nat.

Definition putnam_2008_a3_cont
    {n : nat} (s : Fin.t n -> nat) : Prop :=
  exists j k : Fin.t n,
    putnam_2008_a3_index_lt j k /\
    ~ Nat.divide (s j) (s k).

Definition putnam_2008_a3_init
    {n : nat} (a : Fin.t n -> nat)
    (P : nat -> Fin.t n -> nat) : Prop :=
  P 0%nat = a.

Definition putnam_2008_a3_trans
    {n : nat} (P : nat -> Fin.t n -> nat) : Prop :=
  forall t : nat,
    putnam_2008_a3_cont (P t) ->
    exists j k : Fin.t n,
      putnam_2008_a3_index_lt j k /\
      ~ Nat.divide (P t j) (P t k) /\
      P (t + 1)%nat j = Nat.gcd (P t j) (P t k) /\
      P (t + 1)%nat k = Nat.lcm (P t j) (P t k) /\
      forall i : Fin.t n,
        i <> j ->
        i <> k ->
        P (t + 1)%nat i = P t i.

Theorem putnam_2008_a3
    (n : nat)
    (npos : (0 < n)%nat)
    (a : Fin.t n -> nat)
    (apos : forall i : Fin.t n, (0 < a i)%nat) :
  exists f : Fin.t n -> nat,
    forall P : nat -> Fin.t n -> nat,
      putnam_2008_a3_init a P ->
      putnam_2008_a3_trans P ->
      exists t : nat,
        ~ putnam_2008_a3_cont (P t) /\
        P t = f.
Admitted.
