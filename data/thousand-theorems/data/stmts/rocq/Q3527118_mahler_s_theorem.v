(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527118
  (thousand-theorems__rocq__Q3527118), "Mahler's theorem": every continuous
  function from the p-adic integers to a complete nonarchimedean normed
  p-adic module is the uniform sum of its Mahler series, whose coefficients
  are its iterated forward differences at zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3527118_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1%nat \/ d = p.

Fixpoint q3527118_nat_choose
    (n k : nat) {struct n} : nat :=
  match n with
  | O =>
      match k with
      | O => 1
      | S _ => 0
      end
  | S m =>
      match k with
      | O => 1
      | S j =>
          q3527118_nat_choose m j +
          q3527118_nat_choose m (S j)
      end
  end.

Record q3527118_padic_integers
    (p : nat) (Zp : Type) : Type := {
  q3527118_pzero : Zp;
  q3527118_pone : Zp;
  q3527118_padd : Zp -> Zp -> Zp;
  q3527118_pmul : Zp -> Zp -> Zp;
  q3527118_pneg : Zp -> Zp;
  q3527118_pnorm : Zp -> R;
  q3527118_nat_cast : nat -> Zp;
  q3527118_choose : Zp -> nat -> Zp;

  q3527118_padd_assoc :
    forall x y z : Zp,
      q3527118_padd x (q3527118_padd y z) =
      q3527118_padd (q3527118_padd x y) z;
  q3527118_padd_comm :
    forall x y : Zp, q3527118_padd x y = q3527118_padd y x;
  q3527118_padd_zero :
    forall x : Zp, q3527118_padd x q3527118_pzero = x;
  q3527118_padd_neg :
    forall x : Zp,
      q3527118_padd x (q3527118_pneg x) = q3527118_pzero;
  q3527118_pmul_assoc :
    forall x y z : Zp,
      q3527118_pmul x (q3527118_pmul y z) =
      q3527118_pmul (q3527118_pmul x y) z;
  q3527118_pmul_comm :
    forall x y : Zp, q3527118_pmul x y = q3527118_pmul y x;
  q3527118_pmul_one :
    forall x : Zp, q3527118_pmul x q3527118_pone = x;
  q3527118_pmul_add :
    forall x y z : Zp,
      q3527118_pmul x (q3527118_padd y z) =
      q3527118_padd
        (q3527118_pmul x y) (q3527118_pmul x z);

  q3527118_pnorm_nonnegative :
    forall x : Zp, 0 <= q3527118_pnorm x;
  q3527118_pnorm_eq_zero :
    forall x : Zp,
      q3527118_pnorm x = 0 <-> x = q3527118_pzero;
  q3527118_pnorm_neg :
    forall x : Zp,
      q3527118_pnorm (q3527118_pneg x) = q3527118_pnorm x;
  q3527118_pnorm_add_ultrametric :
    forall x y : Zp,
      q3527118_pnorm (q3527118_padd x y) <=
      Rmax (q3527118_pnorm x) (q3527118_pnorm y);
  q3527118_pnorm_mul :
    forall x y : Zp,
      q3527118_pnorm (q3527118_pmul x y) =
      q3527118_pnorm x * q3527118_pnorm y;
  q3527118_pnorm_one :
    q3527118_pnorm q3527118_pone = 1;

  q3527118_nat_cast_zero :
    q3527118_nat_cast 0 = q3527118_pzero;
  q3527118_nat_cast_one :
    q3527118_nat_cast 1 = q3527118_pone;
  q3527118_nat_cast_add :
    forall m n : nat,
      q3527118_nat_cast (m + n) =
      q3527118_padd (q3527118_nat_cast m) (q3527118_nat_cast n);
  q3527118_nat_cast_mul :
    forall m n : nat,
      q3527118_nat_cast (m * n) =
      q3527118_pmul (q3527118_nat_cast m) (q3527118_nat_cast n);

  q3527118_padic_ball_divisibility :
    forall (x : Zp) (k : nat),
      q3527118_pnorm x <= (/ INR p) ^ k <->
      exists y : Zp,
        x =
        q3527118_pmul
          (q3527118_nat_cast (Nat.pow p k)) y;

  q3527118_padic_complete :
    forall u : nat -> Zp,
      (forall epsilon : R,
        0 < epsilon ->
        exists N : nat,
          forall m n : nat,
            (N <= m)%nat ->
            (N <= n)%nat ->
            q3527118_pnorm
              (q3527118_padd
                (u m) (q3527118_pneg (u n))) < epsilon) ->
      exists limit : Zp,
        forall epsilon : R,
          0 < epsilon ->
          exists N : nat,
            forall n : nat,
              (N <= n)%nat ->
              q3527118_pnorm
                (q3527118_padd
                  (u n) (q3527118_pneg limit)) < epsilon;
  q3527118_nat_cast_dense :
    forall (x : Zp) (epsilon : R),
      0 < epsilon ->
      exists n : nat,
        q3527118_pnorm
          (q3527118_padd
            x (q3527118_pneg (q3527118_nat_cast n))) < epsilon;

  q3527118_choose_nat :
    forall m k : nat,
      q3527118_choose (q3527118_nat_cast m) k =
      q3527118_nat_cast (q3527118_nat_choose m k);
  q3527118_choose_continuous :
    forall (k : nat) (x : Zp) (epsilon : R),
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall y : Zp,
          q3527118_pnorm
            (q3527118_padd y (q3527118_pneg x)) < delta ->
          q3527118_pnorm
            (q3527118_padd
              (q3527118_choose y k)
              (q3527118_pneg (q3527118_choose x k))) < epsilon
}.

Arguments q3527118_pzero {p Zp} _.
Arguments q3527118_pone {p Zp} _.
Arguments q3527118_padd {p Zp} _ _ _.
Arguments q3527118_pmul {p Zp} _ _ _.
Arguments q3527118_pneg {p Zp} _ _.
Arguments q3527118_pnorm {p Zp} _ _.
Arguments q3527118_nat_cast {p Zp} _ _.
Arguments q3527118_choose {p Zp} _ _ _.

Record q3527118_padic_banach_module
    (p : nat) (Zp E : Type)
    (P : q3527118_padic_integers p Zp) : Type := {
  q3527118_vzero : E;
  q3527118_vadd : E -> E -> E;
  q3527118_vneg : E -> E;
  q3527118_smul : Zp -> E -> E;
  q3527118_vnorm : E -> R;

  q3527118_vadd_assoc :
    forall x y z : E,
      q3527118_vadd x (q3527118_vadd y z) =
      q3527118_vadd (q3527118_vadd x y) z;
  q3527118_vadd_comm :
    forall x y : E, q3527118_vadd x y = q3527118_vadd y x;
  q3527118_vadd_zero :
    forall x : E, q3527118_vadd x q3527118_vzero = x;
  q3527118_vadd_neg :
    forall x : E,
      q3527118_vadd x (q3527118_vneg x) = q3527118_vzero;

  q3527118_smul_one :
    forall x : E, q3527118_smul (q3527118_pone P) x = x;
  q3527118_smul_mul :
    forall (a b : Zp) (x : E),
      q3527118_smul (q3527118_pmul P a b) x =
      q3527118_smul a (q3527118_smul b x);
  q3527118_smul_add_scalar :
    forall (a b : Zp) (x : E),
      q3527118_smul (q3527118_padd P a b) x =
      q3527118_vadd (q3527118_smul a x) (q3527118_smul b x);
  q3527118_smul_add_vector :
    forall (a : Zp) (x y : E),
      q3527118_smul a (q3527118_vadd x y) =
      q3527118_vadd (q3527118_smul a x) (q3527118_smul a y);

  q3527118_vnorm_nonnegative :
    forall x : E, 0 <= q3527118_vnorm x;
  q3527118_vnorm_eq_zero :
    forall x : E,
      q3527118_vnorm x = 0 <-> x = q3527118_vzero;
  q3527118_vnorm_neg :
    forall x : E,
      q3527118_vnorm (q3527118_vneg x) = q3527118_vnorm x;
  q3527118_vnorm_add_ultrametric :
    forall x y : E,
      q3527118_vnorm (q3527118_vadd x y) <=
      Rmax (q3527118_vnorm x) (q3527118_vnorm y);
  q3527118_vnorm_smul_le :
    forall (a : Zp) (x : E),
      q3527118_vnorm (q3527118_smul a x) <=
      q3527118_pnorm P a * q3527118_vnorm x;

  q3527118_module_complete :
    forall u : nat -> E,
      (forall epsilon : R,
        0 < epsilon ->
        exists N : nat,
          forall m n : nat,
            (N <= m)%nat ->
            (N <= n)%nat ->
            q3527118_vnorm
              (q3527118_vadd
                (u m) (q3527118_vneg (u n))) < epsilon) ->
      exists limit : E,
        forall epsilon : R,
          0 < epsilon ->
          exists N : nat,
            forall n : nat,
              (N <= n)%nat ->
              q3527118_vnorm
                (q3527118_vadd
                  (u n) (q3527118_vneg limit)) < epsilon
}.

Arguments q3527118_vzero {p Zp E P} _.
Arguments q3527118_vadd {p Zp E P} _ _ _.
Arguments q3527118_vneg {p Zp E P} _ _.
Arguments q3527118_smul {p Zp E P} _ _ _.
Arguments q3527118_vnorm {p Zp E P} _ _.

Definition q3527118_psub
    {p : nat} {Zp : Type}
    (P : q3527118_padic_integers p Zp)
    (x y : Zp) : Zp :=
  q3527118_padd P x (q3527118_pneg P y).

Definition q3527118_vsub
    {p : nat} {Zp E : Type}
    {P : q3527118_padic_integers p Zp}
    (V : @q3527118_padic_banach_module p Zp E P)
    (x y : E) : E :=
  q3527118_vadd V x (q3527118_vneg V y).

Definition q3527118_continuous
    {p : nat} {Zp E : Type}
    {P : q3527118_padic_integers p Zp}
    (V : @q3527118_padic_banach_module p Zp E P)
    (f : Zp -> E) : Prop :=
  forall (x : Zp) (epsilon : R),
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : Zp,
        q3527118_pnorm P (q3527118_psub P y x) < delta ->
        q3527118_vnorm V
          (q3527118_vsub V (f y) (f x)) < epsilon.

Fixpoint q3527118_fwd_diff_iter
    {p : nat} {Zp E : Type}
    {P : q3527118_padic_integers p Zp}
    (V : @q3527118_padic_banach_module p Zp E P)
    (f : Zp -> E) (n : nat) (x : Zp) : E :=
  match n with
  | O => f x
  | S k =>
      q3527118_vsub V
        (q3527118_fwd_diff_iter V f k
          (q3527118_padd P x (q3527118_pone P)))
        (q3527118_fwd_diff_iter V f k x)
  end.

Definition q3527118_mahler_term
    {p : nat} {Zp E : Type}
    {P : q3527118_padic_integers p Zp}
    (V : @q3527118_padic_banach_module p Zp E P)
    (f : Zp -> E) (n : nat) (x : Zp) : E :=
  q3527118_smul V
    (q3527118_choose P x n)
    (q3527118_fwd_diff_iter V f n (q3527118_pzero P)).

Fixpoint q3527118_finite_sum
    {p : nat} {Zp E : Type}
    {P : q3527118_padic_integers p Zp}
    (V : @q3527118_padic_banach_module p Zp E P)
    (terms : nat -> Zp -> E)
    (indices : list nat) (x : Zp) : E :=
  match indices with
  | nil => q3527118_vzero V
  | cons n rest =>
      q3527118_vadd V
        (terms n x) (q3527118_finite_sum V terms rest x)
  end.

Definition q3527118_contains
    (base candidate : list nat) : Prop :=
  forall n : nat, In n base -> In n candidate.

Definition q3527118_has_uniform_sum
    {p : nat} {Zp E : Type}
    {P : q3527118_padic_integers p Zp}
    (V : @q3527118_padic_banach_module p Zp E P)
    (terms : nat -> Zp -> E)
    (sum : Zp -> E) : Prop :=
  (forall n : nat, q3527118_continuous V (terms n)) /\
  forall epsilon : R,
    0 < epsilon ->
    exists base : list nat,
      NoDup base /\
      forall indices : list nat,
        NoDup indices ->
        q3527118_contains base indices ->
        forall x : Zp,
          q3527118_vnorm V
            (q3527118_vsub V
              (q3527118_finite_sum V terms indices x)
              (sum x)) < epsilon.

Module PadicInt.

Theorem hasSum_mahler :
  forall (p : nat),
    q3527118_prime p ->
    forall (Zp E : Type)
           (P : q3527118_padic_integers p Zp)
           (V : @q3527118_padic_banach_module p Zp E P)
           (f : Zp -> E),
      q3527118_continuous V f ->
      q3527118_has_uniform_sum V
        (q3527118_mahler_term V f) f.
Admitted.

End PadicInt.
