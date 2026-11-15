(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2919401
  (thousand-theorems__rocq__Q2919401), "Ostrowski's theorem": every nontrivial
  real-valued absolute value on the rationals is equivalent either to the
  standard absolute value or, for a unique prime p, to the p-adic absolute
  value. This file contains no proof.
*)

From Stdlib Require Import
  Arith.PeanoNat QArith.QArith Reals.

Open Scope R_scope.

Definition q2919401_is_absolute_value (v : Q -> R) : Prop :=
  (forall x y : Q, Qeq x y -> v x = v y) /\
  (forall x y : Q, v (Qmult x y) = v x * v y) /\
  (forall x : Q, 0 <= v x) /\
  (forall x : Q, v x = 0 <-> Qeq x 0%Q) /\
  (forall x y : Q, v (Qplus x y) <= v x + v y).

Definition q2919401_is_nontrivial (v : Q -> R) : Prop :=
  exists x : Q, ~ Qeq x 0%Q /\ v x <> 1.

Definition q2919401_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1%nat \/ d = p.

Definition q2919401_p_order
    (p n k : nat) : Prop :=
  n <> 0%nat /\
  Nat.divide (Nat.pow p k) n /\
  ~ Nat.divide (Nat.pow p (S k)) n.

Definition q2919401_real_power
    (base exponent : R) : R :=
  if Rlt_dec 0 base
  then Rpower base exponent
  else 0.

Definition q2919401_equivalent_to_real
    (v : Q -> R) : Prop :=
  exists c : R,
    0 < c /\
    forall x : Q,
      q2919401_real_power (v x) c = Rabs (Q2R x).

Definition q2919401_equivalent_to_padic
    (v : Q -> R) (p : nat) : Prop :=
  exists c : R,
    0 < c /\
    forall x : Q,
      (Qeq x 0%Q /\ q2919401_real_power (v x) c = 0) \/
      (~ Qeq x 0%Q /\
       exists numerator_order denominator_order : nat,
         q2919401_p_order
           p (Z.abs_nat (Qnum x)) numerator_order /\
         q2919401_p_order
           p (Pos.to_nat (Qden x)) denominator_order /\
         q2919401_real_power (v x) c =
           powerRZ
             (INR p)
             (Z.of_nat denominator_order -
              Z.of_nat numerator_order)%Z).

Theorem Rat_AbsoluteValue_equiv_real_or_padic :
  forall f : Q -> R,
    q2919401_is_absolute_value f ->
    q2919401_is_nontrivial f ->
    q2919401_equivalent_to_real f \/
    exists p : nat,
      q2919401_prime p /\
      q2919401_equivalent_to_padic f p /\
      forall q : nat,
        q2919401_prime q ->
        q2919401_equivalent_to_padic f q ->
        q = p.
Admitted.
