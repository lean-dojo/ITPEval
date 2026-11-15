(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Lra.
From Stdlib Require Import Rbase.
From Stdlib Require Import PSeries_reg.
From Stdlib Require Import Rtrigo1.
From Stdlib Require Import Rtrigo_facts.
From Stdlib Require Import Ranalysis_reg.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import AltSeries.
From Stdlib Require Import Rseries.
From Stdlib Require Import SeqProp.
From Stdlib Require Import Ranalysis5.
From Stdlib Require Import SeqSeries.
From Stdlib Require Import PartSum.
From Stdlib Require Import Lia.
From Stdlib Require Import Znat.

#[local] Open Scope R_scope.
#[local] Ltac Tauto.intuition_solver ::= auto with rorders real arith.

(*********************************************************)
(** * Preliminaries                                      *)
(*********************************************************)

(** ** Various generic lemmas which probably should go somewhere else *)

Lemma Boule_half_to_interval : forall x,
  Boule (/2) posreal_half x -> 0 <= x <= 1.
Proof.
Admitted.

Lemma ub_opp : forall x, x < PI/2 -> -PI/2 < -x.
Proof.
Admitted.

Definition atan x := let (v, _) := pre_atan x in v.

Lemma atan_bound : forall x,
  -PI/2 < atan x < PI/2.
Proof.
Admitted.

Lemma Ratan_seq_opp : forall x n,
  Ratan_seq (-x) n = -Ratan_seq x n.
Proof.
Admitted.

Definition in_int (x : R) : {-1 <= x <= 1}+{~ -1 <= x <= 1}.
Proof.
Admitted.

Definition ps_atan (x : R) : R :=
 match in_int x with
   left h => let (v, _) := ps_atan_exists_1 x h in v
 | right h => atan x
 end.

(** ** Proof of the equivalence of the two definitions between -1 and 1 *)

Lemma ps_atan0_0 : ps_atan 0 = 0.
Proof.
Admitted.

Lemma ps_atan_exists_1_opp : forall x h h',
  proj1_sig (ps_atan_exists_1 (-x) h) = -(proj1_sig (ps_atan_exists_1 x h')).
Proof.
Admitted.

Lemma ps_atan_opp : forall x,
  ps_atan (-x) = -ps_atan x.
Proof.
Admitted.

(** atan = ps_atan *)

Lemma ps_atanSeq_continuity_pt_1 : forall (N : nat) (x : R),
  0 <= x -> x <= 1 ->
  continuity_pt (fun x => sum_f_R0 (tg_alt (Ratan_seq x)) N) x.
Proof.
Admitted.

(** Definition of ps_atan's derivative *)

Definition Datan_seq := fun (x : R) (n : nat) => x ^ (2*n).

Lemma pow_lt_1_compat : forall x n,
  0 <= x < 1 -> (0 < n)%nat ->
  0 <= x ^ n < 1.
Proof.
Admitted.

Lemma Datan_seq_Rabs : forall x n,
  Datan_seq (Rabs x) n = Datan_seq x n.
Proof.
Admitted.

Lemma Datan_seq_pos : forall x n, 0 < x ->
  0 < Datan_seq x n.
Proof.
Admitted.

Lemma Datan_sum_eq :forall x n,
  sum_f_R0 (tg_alt (Datan_seq x)) n = (1 - (- x ^ 2) ^ S n)/(1 + x ^ 2).
Proof.
Admitted.

Lemma Datan_seq_increasing : forall x y n,
  (n > 0)%nat -> 0 <= x < y ->
  Datan_seq x n < Datan_seq y n.
Proof.
Admitted.

Lemma Datan_seq_decreasing : forall x, -1 < x -> x < 1 ->
  Un_decreasing (Datan_seq x).
Proof.
Admitted.

Lemma Datan_seq_CV_0 : forall x, -1 < x -> x < 1 ->
  Un_cv (Datan_seq x) 0.
Proof.
Admitted.

Lemma Datan_lim : forall x, -1 < x -> x < 1 ->
  Un_cv (fun N : nat => sum_f_R0 (tg_alt (Datan_seq x)) N) (/ (1 + x ^ 2)).
Proof.
Admitted.

Lemma Datan_CVU_prelim : forall c (r : posreal), Rabs c + r < 1 ->
  CVU (fun N x => sum_f_R0 (tg_alt (Datan_seq x)) N)
      (fun y : R => / (1 + y ^ 2)) c r.
Proof.
Admitted.

Lemma Datan_is_datan : forall (N : nat) (x : R),
  -1 <= x -> x < 1 ->
  derivable_pt_lim (fun x => sum_f_R0 (tg_alt (Ratan_seq x)) N) x (sum_f_R0 (tg_alt (Datan_seq x)) N).
Proof.
Admitted.

Lemma Ratan_CVU' :
  CVU (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N)
      ps_atan (/2) posreal_half.
Proof.
Admitted.

Lemma Ratan_CVU :
  CVU (fun N x => sum_f_R0 (tg_alt (Ratan_seq x)) N)
      ps_atan 0 (mkposreal 1 Rlt_0_1).
Proof.
Admitted.

Lemma Alt_PI_tg : forall n, PI_tg n = Ratan_seq 1 n.
Proof.
Admitted.

Lemma Ratan_is_ps_atan : forall eps, eps > 0 ->
  exists N, forall n, (n >= N)%nat -> forall x, -1 < x -> x < 1 ->
  Rabs (sum_f_R0 (tg_alt (Ratan_seq x)) n - ps_atan x) < eps.
Proof.
Admitted.

Lemma Datan_continuity : continuity (fun x => /(1 + x^2)).
Proof.
Admitted.

Lemma derivable_pt_lim_ps_atan : forall x, -1 < x < 1 ->
  derivable_pt_lim ps_atan x ((fun y => /(1 + y ^ 2)) x).
Proof.
Admitted.

Lemma derivable_pt_ps_atan : forall x, -1 < x < 1 ->
  derivable_pt ps_atan x.
Proof.
Admitted.

Lemma ps_atan_continuity_pt_1 : forall eps : R,
  eps > 0 ->
  exists alp : R, alp > 0 /\ (forall x, x < 1 -> 0 < x -> Rdist x 1 < alp ->
  dist R_met (ps_atan x) (Alt_PI/4) < eps).
Proof.
Admitted.

Lemma Datan_eq_DatanSeq_interv : forall x, -1 < x < 1 ->
  forall (Pratan:derivable_pt ps_atan x) (Prmymeta:derivable_pt atan x),
    derive_pt ps_atan x Pratan = derive_pt atan x Prmymeta.
Proof.
Admitted.

Lemma atan_eq_ps_atan : forall x, 0 < x < 1 ->
  atan x = ps_atan x.
Proof.
Admitted.

Theorem Alt_PI_eq : Alt_PI = PI.
Proof.
Admitted.

Lemma PI_ineq : forall N : nat,
  sum_f_R0 (tg_alt PI_tg) (S (2 * N)) <= PI/4 <= sum_f_R0 (tg_alt PI_tg) (2 * N).
Proof.
Admitted.

(** ** Relation between arctangent and sine and cosine *)

Lemma sin_atan: forall x,
  sin (atan x) = x / sqrt (1 + x²).
Proof.
Admitted.

Lemma cos_atan: forall x,
  cos (atan x) = 1 / sqrt(1 + x²).
Proof.
Admitted.

(*********************************************************)
(** * Definition of arcsine based on arctangent          *)
(*********************************************************)

(** asin is defined by cases so that it is defined in the full range from -1 .. 1 *)

Definition asin x :=
  if Rle_dec x (-1) then - (PI / 2) else
  if Rle_dec 1 x then PI / 2 else
  atan (x / sqrt (1 - x²)).

(** ** Relation between arcsin and arctangent *)

Lemma asin_atan : forall x, -1 < x < 1 ->
  asin x = atan (x / sqrt (1 - x²)).
Proof.
Admitted.

(** ** arcsine of specific values *)

Lemma asin_0 : asin 0 = 0.
Proof.
Admitted.

Lemma asin_1 : asin 1 = PI / 2.
Proof.
Admitted.

Lemma asin_inv_sqrt2 : asin (/sqrt 2) = PI/4.
Proof.
Admitted.

Lemma asin_opp : forall x,
  asin (- x) = - asin x.
Proof.
Admitted.

(** ** Bounds of arcsine *)

Lemma asin_bound : forall x,
  - (PI/2) <= asin x <= PI/2.
Proof.
Admitted.

Lemma asin_bound_lt : forall x, -1 < x < 1 ->
  - (PI/2) < asin x < PI/2.
Proof.
Admitted.

(** ** arcsine is the left and right inverse of sine *)

Lemma sin_asin : forall x, -1 <= x <= 1 ->
  sin (asin x) = x.
Proof.
Admitted.

Lemma asin_sin : forall x, -(PI/2) <= x <= PI/2 ->
  asin (sin x) = x.
Proof.
Admitted.

(** ** Relation between arcsin, cosine and tangent *)

Lemma cos_asin : forall x, -1 <= x <= 1 ->
  cos (asin x) = sqrt (1 - x²).
Proof.
Admitted.

Lemma tan_asin : forall x, -1 <= x <= 1 ->
  tan (asin x) = x / sqrt (1 - x²).
Proof.
Admitted.

(** ** Derivative of arcsine *)

Lemma derivable_pt_asin : forall x, -1 < x < 1 ->
  derivable_pt asin x.
Proof.
Admitted.

Lemma derive_pt_asin : forall (x : R) (Hxrange : -1 < x < 1),
   derive_pt asin x (derivable_pt_asin x Hxrange) = 1 / sqrt (1 - x²).
Proof.
Admitted.

(*********************************************************)
(** * Definition of arccosine based on arctangent        *)
(*********************************************************)

(** acos is defined by cases so that it is defined in the full range from -1 .. 1 *)

Definition acos x :=
  if Rle_dec x (-1) then PI else
  if Rle_dec 1 x then 0 else
  PI/2 - atan (x/sqrt(1 - x²)).

(** ** Relation between arccosine, arcsine and arctangent *)

Lemma acos_atan : forall x, 0 < x ->
  acos x = atan (sqrt (1 - x²) / x).
Proof.
Admitted.

Lemma acos_asin : forall x, -1 <= x <= 1 ->
  acos x = PI/2 - asin x.
Proof.
Admitted.

Lemma asin_acos : forall x, -1 <= x <= 1 ->
  asin x = PI/2 - acos x.
Proof.
Admitted.

(** ** arccosine of specific values *)

Lemma acos_0 : acos 0 = PI/2.
Proof.
Admitted.

Lemma acos_1 : acos 1 = 0.
Proof.
Admitted.

Lemma acos_opp : forall x,
  acos (- x) = PI - acos x.
Proof.
Admitted.

Lemma acos_inv_sqrt2 : acos (/sqrt 2) = PI/4.
Proof.
Admitted.

(** ** Bounds of arccosine *)

Lemma acos_bound : forall x,
  0 <= acos x <= PI.
Proof.
Admitted.

Lemma acos_bound_lt : forall x, -1 < x < 1 ->
  0 < acos x < PI.
Proof.
Admitted.

(** ** arccosine is the left and right inverse of cosine *)

Lemma cos_acos : forall x, -1 <= x <= 1 ->
  cos (acos x) = x.
Proof.
Admitted.

Lemma acos_cos : forall x, 0 <= x <= PI ->
  acos (cos x) = x.
Proof.
Admitted.

(** ** Relation between arccosine, sine and tangent *)

Lemma sin_acos : forall x, -1 <= x <= 1 ->
  sin (acos x) = sqrt (1 - x²).
Proof.
Admitted.

Lemma tan_acos : forall x, -1 <= x <= 1 ->
  tan (acos x) = sqrt (1 - x²) / x.
Proof.
Admitted.

(** ** Derivative of arccosine *)

Lemma derivable_pt_acos : forall x, -1 < x < 1 ->
  derivable_pt acos x.
Proof.
Admitted.

Lemma derive_pt_acos : forall (x : R) (Hxrange : -1 < x < 1),
   derive_pt acos x (derivable_pt_acos x Hxrange) = -1 / sqrt (1 - x²).
Proof.
Admitted.

Lemma sin_gt_x x : x < 0 -> x < sin x.
Proof.
Admitted.
