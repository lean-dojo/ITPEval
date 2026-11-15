(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Rbase.
From Stdlib Require Import Rfunctions.
From Stdlib Require Import SeqSeries.
From Stdlib Require Import Rtrigo1.
From Stdlib Require Import R_sqrt.
#[local] Open Scope R_scope.

(** * Distance *)

Definition dist_euc (x0 y0 x1 y1:R) : R :=
  sqrt (Rsqr (x0 - x1) + Rsqr (y0 - y1)).

Lemma distance_refl : forall x0 y0:R, dist_euc x0 y0 x0 y0 = 0.
Proof.
Admitted.

Lemma distance_symm :
  forall x0 y0 x1 y1:R, dist_euc x0 y0 x1 y1 = dist_euc x1 y1 x0 y0.
Proof.
Admitted.

Lemma law_cosines :
  forall x0 y0 x1 y1 x2 y2 ac:R,
    let a := dist_euc x1 y1 x0 y0 in
      let b := dist_euc x2 y2 x0 y0 in
        let c := dist_euc x2 y2 x1 y1 in
          a * c * cos ac = (x0 - x1) * (x2 - x1) + (y0 - y1) * (y2 - y1) ->
          Rsqr b = Rsqr c + Rsqr a - 2 * (a * c * cos ac).
Proof.
Admitted.

Lemma triangle :
  forall x0 y0 x1 y1 x2 y2:R,
    dist_euc x0 y0 x1 y1 <= dist_euc x0 y0 x2 y2 + dist_euc x2 y2 x1 y1.
Proof.
Admitted.

(******************************************************************)
(** *                       Translation                           *)
(******************************************************************)

Definition xt (x tx:R) : R := x + tx.
Definition yt (y ty:R) : R := y + ty.

Lemma translation_0 : forall x y:R, xt x 0 = x /\ yt y 0 = y.
Proof.
Admitted.

Lemma isometric_translation :
  forall x1 x2 y1 y2 tx ty:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xt x1 tx - xt x2 tx) + Rsqr (yt y1 ty - yt y2 ty).
Proof.
Admitted.

(******************************************************************)
(** *                         Rotation                            *)
(******************************************************************)

Definition xr (x y theta:R) : R := x * cos theta + y * sin theta.
Definition yr (x y theta:R) : R := - x * sin theta + y * cos theta.

Lemma rotation_0 : forall x y:R, xr x y 0 = x /\ yr x y 0 = y.
Proof.
Admitted.

Lemma rotation_PI2 :
  forall x y:R, xr x y (PI / 2) = y /\ yr x y (PI / 2) = - x.
Proof.
Admitted.

Lemma isometric_rotation_0 :
  forall x1 y1 x2 y2 theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xr x1 y1 theta - xr x2 y2 theta) +
    Rsqr (yr x1 y1 theta - yr x2 y2 theta).
Proof.
Admitted.

Lemma isometric_rotation :
  forall x1 y1 x2 y2 theta:R,
    dist_euc x1 y1 x2 y2 =
    dist_euc (xr x1 y1 theta) (yr x1 y1 theta) (xr x2 y2 theta)
    (yr x2 y2 theta).
Proof.
Admitted.

(******************************************************************)
(** *                       Similarity                            *)
(******************************************************************)

Lemma isometric_rot_trans :
  forall x1 y1 x2 y2 tx ty theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xr (xt x1 tx) (yt y1 ty) theta - xr (xt x2 tx) (yt y2 ty) theta) +
    Rsqr (yr (xt x1 tx) (yt y1 ty) theta - yr (xt x2 tx) (yt y2 ty) theta).
Proof.
Admitted.

Lemma isometric_trans_rot :
  forall x1 y1 x2 y2 tx ty theta:R,
    Rsqr (x1 - x2) + Rsqr (y1 - y2) =
    Rsqr (xt (xr x1 y1 theta) tx - xt (xr x2 y2 theta) tx) +
    Rsqr (yt (yr x1 y1 theta) ty - yt (yr x2 y2 theta) ty).
Proof.
Admitted.
