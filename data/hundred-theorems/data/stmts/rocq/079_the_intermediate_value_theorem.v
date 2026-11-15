(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Sumbool.
From Stdlib Require Import Rbase.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import SeqSeries.
From Stdlib Require Import Ranalysis1.
From Stdlib Require Import Lra.
#[local] Open Scope R_scope.

Fixpoint Dichotomy_lb (x y:R) (P:R -> bool) (N:nat) {struct N} : R :=
  match N with
    | O => x
    | S n =>
      let down := Dichotomy_lb x y P n in
        let up := Dichotomy_ub x y P n in
          let z := (down + up) / 2 in if P z then down else z
  end

  with Dichotomy_ub (x y:R) (P:R -> bool) (N:nat) {struct N} : R :=
    match N with
      | O => y
      | S n =>
        let down := Dichotomy_lb x y P n in
          let up := Dichotomy_ub x y P n in
            let z := (down + up) / 2 in if P z then z else up
    end.

Definition dicho_lb (x y:R) (P:R -> bool) (N:nat) : R := Dichotomy_lb x y P N.
Definition dicho_up (x y:R) (P:R -> bool) (N:nat) : R := Dichotomy_ub x y P N.

(**********)
Lemma dicho_comp :
  forall (x y:R) (P:R -> bool) (n:nat),
    x <= y -> dicho_lb x y P n <= dicho_up x y P n.
Proof.
Admitted.

Lemma dicho_lb_growing :
  forall (x y:R) (P:R -> bool), x <= y -> Un_growing (dicho_lb x y P).
Proof.
Admitted.

Lemma dicho_up_decreasing :
  forall (x y:R) (P:R -> bool), x <= y -> Un_decreasing (dicho_up x y P).
Proof.
Admitted.

Lemma dicho_lb_maj_y :
  forall (x y:R) (P:R -> bool), x <= y -> forall n:nat, dicho_lb x y P n <= y.
Proof.
Admitted.

Lemma dicho_lb_maj :
  forall (x y:R) (P:R -> bool), x <= y -> has_ub (dicho_lb x y P).
Proof.
Admitted.

Lemma dicho_up_min_x :
  forall (x y:R) (P:R -> bool), x <= y -> forall n:nat, x <= dicho_up x y P n.
Proof.
Admitted.

Lemma dicho_up_min :
  forall (x y:R) (P:R -> bool), x <= y -> has_lb (dicho_up x y P).
Proof.
Admitted.

Lemma dicho_lb_cv :
  forall (x y:R) (P:R -> bool),
    x <= y -> { l:R | Un_cv (dicho_lb x y P) l }.
Proof.
Admitted.

Lemma dicho_up_cv :
  forall (x y:R) (P:R -> bool),
    x <= y -> { l:R | Un_cv (dicho_up x y P) l }.
Proof.
Admitted.

Lemma dicho_lb_dicho_up :
  forall (x y:R) (P:R -> bool) (n:nat),
    x <= y -> dicho_up x y P n - dicho_lb x y P n = (y - x) / 2 ^ n.
Proof.
Admitted.

Definition pow_2_n (n:nat) := 2 ^ n.

Lemma pow_2_n_neq_R0 : forall n:nat, pow_2_n n <> 0.
Proof.
Admitted.

Lemma pow_2_n_growing : Un_growing pow_2_n.
Proof.
Admitted.

Lemma pow_2_n_infty : cv_infty pow_2_n.
Proof.
Admitted.

Lemma cv_dicho :
  forall (x y l1 l2:R) (P:R -> bool),
    x <= y ->
    Un_cv (dicho_lb x y P) l1 -> Un_cv (dicho_up x y P) l2 -> l1 = l2.
Proof.
Admitted.

Definition cond_positivity (x:R) : bool :=
  match Rle_dec 0 x with
    | left _ => true
    | right _ => false
  end.

(** Sequential characterisation of continuity *)
Lemma continuity_seq :
  forall (f:R -> R) (Un:nat -> R) (l:R),
    continuity_pt f l -> Un_cv Un l -> Un_cv (fun i:nat => f (Un i)) (f l).
Proof.
Admitted.

Lemma dicho_lb_car :
  forall (x y:R) (P:R -> bool) (n:nat),
    P x = false -> P (dicho_lb x y P n) = false.
Proof.
Admitted.

Lemma dicho_up_car :
  forall (x y:R) (P:R -> bool) (n:nat),
    P y = true -> P (dicho_up x y P n) = true.
Proof.
Admitted.

(* A general purpose corollary. *)
Lemma cv_pow_half : forall a, Un_cv (fun n => a/2^n) 0.
Proof.
Admitted.

(** Intermediate Value Theorem *)
Lemma IVT :
  forall (f:R -> R) (x y:R),
    continuity f ->
    x < y -> f x < 0 -> 0 < f y -> { z:R | x <= z <= y /\ f z = 0 }.
Proof.
Admitted.

Lemma IVT_cor :
  forall (f:R -> R) (x y:R),
    continuity f ->
    x <= y -> f x * f y <= 0 -> { z:R | x <= z <= y /\ f z = 0 }.
Proof.
Admitted.

(** We can now define the square root function as the reciprocal
   transformation of the square function *)
Lemma Rsqrt_exists :
  forall y:R, 0 <= y -> { z:R | 0 <= z /\ y = Rsqr z }.
Proof.
Admitted.

(* Definition of the square root: R+->R *)
Definition Rsqrt (y:nonnegreal) : R :=
  let (a,_) := Rsqrt_exists (nonneg y) (cond_nonneg y) in a.

(**********)
Lemma Rsqrt_positivity : forall x:nonnegreal, 0 <= Rsqrt x.
Proof.
Admitted.

(**********)
Lemma Rsqrt_Rsqrt : forall x:nonnegreal, Rsqrt x * Rsqrt x = x.
Proof.
Admitted.
