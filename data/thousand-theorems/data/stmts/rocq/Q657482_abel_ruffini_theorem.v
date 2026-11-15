(*
  Statement-only formalization of Thousand Theorems corpus artifact Q657482
  (thousand-theorems__rocq__Q657482), "Abel–Ruffini theorem": there exists a
  complex number algebraic over the rationals that is not solvable by radicals
  over the rationals. This file contains no proof.
*)

From Stdlib Require Import Lists.List QArith.QArith Reals.

Import ListNotations.
Local Open Scope R_scope.

Definition q657482_complex : Type := (R * R)%type.

Definition q657482_czero : q657482_complex := (0, 0).
Definition q657482_cone : q657482_complex := (1, 0).

Definition q657482_cadd
    (z w : q657482_complex) : q657482_complex :=
  (fst z + fst w, snd z + snd w).

Definition q657482_cneg
    (z : q657482_complex) : q657482_complex :=
  (- fst z, - snd z).

Definition q657482_cmul
    (z w : q657482_complex) : q657482_complex :=
  (fst z * fst w - snd z * snd w,
   fst z * snd w + snd z * fst w).

Definition q657482_cinv
    (z : q657482_complex) : q657482_complex :=
  let denominator := fst z * fst z + snd z * snd z in
  (fst z / denominator, - snd z / denominator).

Fixpoint q657482_cpow
    (z : q657482_complex) (n : nat) : q657482_complex :=
  match n with
  | O => q657482_cone
  | S k => q657482_cmul z (q657482_cpow z k)
  end.

Definition q657482_rat_embed (q : Q) : q657482_complex :=
  (Q2R q, 0).

Fixpoint q657482_poly_eval
    (coefficients : list Q)
    (z : q657482_complex) : q657482_complex :=
  match coefficients with
  | [] => q657482_czero
  | coefficient :: higher_coefficients =>
      q657482_cadd
        (q657482_rat_embed coefficient)
        (q657482_cmul z
          (q657482_poly_eval higher_coefficients z))
  end.

Definition q657482_nonzero_polynomial
    (coefficients : list Q) : Prop :=
  exists coefficient : Q,
    In coefficient coefficients /\ ~ Qeq coefficient 0%Q.

Definition q657482_is_algebraic
    (z : q657482_complex) : Prop :=
  exists coefficients : list Q,
    q657482_nonzero_polynomial coefficients /\
    q657482_poly_eval coefficients z = q657482_czero.

Inductive q657482_solvable_by_rad : q657482_complex -> Prop :=
| q657482_sbr_base :
    forall q : Q,
      q657482_solvable_by_rad (q657482_rat_embed q)
| q657482_sbr_add :
    forall z w : q657482_complex,
      q657482_solvable_by_rad z ->
      q657482_solvable_by_rad w ->
      q657482_solvable_by_rad (q657482_cadd z w)
| q657482_sbr_neg :
    forall z : q657482_complex,
      q657482_solvable_by_rad z ->
      q657482_solvable_by_rad (q657482_cneg z)
| q657482_sbr_mul :
    forall z w : q657482_complex,
      q657482_solvable_by_rad z ->
      q657482_solvable_by_rad w ->
      q657482_solvable_by_rad (q657482_cmul z w)
| q657482_sbr_inv :
    forall z : q657482_complex,
      q657482_solvable_by_rad z ->
      q657482_solvable_by_rad (q657482_cinv z)
| q657482_sbr_rad :
    forall (z : q657482_complex) (n : nat),
      n <> O ->
      q657482_solvable_by_rad (q657482_cpow z n) ->
      q657482_solvable_by_rad z.

Theorem AbelRuffini_exists_not_solvable_by_rad :
  exists z : q657482_complex,
    q657482_is_algebraic z /\
    ~ q657482_solvable_by_rad z.
Admitted.
