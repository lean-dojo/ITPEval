(*
  Statement-only formalization of Thousand Theorems corpus artifact Q318767
  (thousand-theorems__rocq__Q318767), "Abel's theorem": convergence of the
  coefficient partial sums implies convergence of the associated complex
  power series within every positive Stolz cone at 1, and of the real power
  series as its argument approaches 1 from the left. This file contains no
  proof.
*)

From Stdlib Require Import
  Reals ClassicalDescription ClassicalEpsilon Arith.PeanoNat.

Local Open Scope R_scope.

Definition q318767_C : Type := (R * R)%type.

Definition q318767_czero : q318767_C := (0, 0).

Definition q318767_cone : q318767_C := (1, 0).

Definition q318767_cadd
    (z w : q318767_C) : q318767_C :=
  (fst z + fst w, snd z + snd w).

Definition q318767_copp
    (z : q318767_C) : q318767_C :=
  (- fst z, - snd z).

Definition q318767_csub
    (z w : q318767_C) : q318767_C :=
  q318767_cadd z (q318767_copp w).

Definition q318767_cmul
    (z w : q318767_C) : q318767_C :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q318767_cnorm
    (z : q318767_C) : R :=
  sqrt (fst z ^ 2 + snd z ^ 2).

Fixpoint q318767_cpow
    (z : q318767_C) (n : nat) : q318767_C :=
  match n with
  | O => q318767_cone
  | S k => q318767_cmul z (q318767_cpow z k)
  end.

Fixpoint q318767_cpartial_sum
    (terms : nat -> q318767_C) (n : nat) : q318767_C :=
  match n with
  | O => q318767_czero
  | S k =>
      q318767_cadd
        (q318767_cpartial_sum terms k) (terms k)
  end.

Definition q318767_csequence_converges
    (sequence : nat -> q318767_C)
    (limit : q318767_C) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q318767_cnorm
          (q318767_csub (sequence n) limit) < epsilon.

Definition q318767_chas_sum
    (terms : nat -> q318767_C)
    (sum : q318767_C) : Prop :=
  q318767_csequence_converges
    (q318767_cpartial_sum terms) sum.

Definition q318767_ctsum
    (terms : nat -> q318767_C) : q318767_C :=
  match excluded_middle_informative
          (exists sum : q318767_C, q318767_chas_sum terms sum) with
  | left _ =>
      epsilon (inhabits q318767_czero)
        (fun sum : q318767_C => q318767_chas_sum terms sum)
  | right _ => q318767_czero
  end.

Definition q318767_complex_power_series
    (f : nat -> q318767_C) (z : q318767_C) : q318767_C :=
  q318767_ctsum
    (fun n : nat => q318767_cmul (f n) (q318767_cpow z n)).

Definition q318767_stolz_cone
    (s : R) (z : q318767_C) : Prop :=
  Rabs (snd z) < s * (1 - fst z).

Definition q318767_ctendsto_within_stolz_cone
    (g : q318767_C -> q318767_C)
    (s : R) (limit : q318767_C) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall z : q318767_C,
        q318767_stolz_cone s z ->
        q318767_cnorm (q318767_csub z q318767_cone) < delta ->
        q318767_cnorm (q318767_csub (g z) limit) < epsilon.

Theorem Complex_tendsto_tsum_powerSeries_nhdsWithin_stolzCone :
  forall (f : nat -> q318767_C) (l : q318767_C) (s : R),
    q318767_chas_sum f l ->
    0 < s ->
    q318767_ctendsto_within_stolz_cone
      (q318767_complex_power_series f) s l.
Admitted.

Fixpoint q318767_rpartial_sum
    (terms : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q318767_rpartial_sum terms k + terms k
  end.

Definition q318767_rsequence_converges
    (sequence : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (sequence n - limit) < epsilon.

Definition q318767_rhas_sum
    (terms : nat -> R) (sum : R) : Prop :=
  q318767_rsequence_converges
    (q318767_rpartial_sum terms) sum.

Definition q318767_rtsum
    (terms : nat -> R) : R :=
  match excluded_middle_informative
          (exists sum : R, q318767_rhas_sum terms sum) with
  | left _ =>
      epsilon (inhabits 0)
        (fun sum : R => q318767_rhas_sum terms sum)
  | right _ => 0
  end.

Definition q318767_real_power_series
    (f : nat -> R) (x : R) : R :=
  q318767_rtsum
    (fun n : nat => f n * x ^ n).

Definition q318767_rtendsto_from_left
    (g : R -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall x : R,
        x < 1 ->
        Rabs (x - 1) < delta ->
        Rabs (g x - limit) < epsilon.

Theorem Real_tendsto_tsum_powerSeries_nhdsWithin_lt :
  forall (f : nat -> R) (l : R),
    q318767_rhas_sum f l ->
    q318767_rtendsto_from_left
      (q318767_real_power_series f) l.
Admitted.
