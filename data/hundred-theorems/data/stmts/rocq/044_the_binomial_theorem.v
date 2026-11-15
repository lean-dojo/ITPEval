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
From Stdlib Require Import PartSum.
From Stdlib Require Import Arith.Factorial.
#[local] Open Scope R_scope.

Definition C (n p:nat) : R :=
  INR (fact n) / (INR (fact p) * INR (fact (n - p))).

Lemma pascal_step1 : forall n i:nat, (i <= n)%nat -> C n i = C n (n - i).
Proof.
Admitted.

Lemma pascal_step2 :
  forall n i:nat,
    (i <= n)%nat -> C (S n) i = INR (S n) / INR (S n - i) * C n i.
Proof.
Admitted.

Lemma pascal_step3 :
  forall n i:nat, (i < n)%nat -> C n (S i) = INR (n - i) / INR (S i) * C n i.
Proof.
Admitted.

  (**********)
Lemma pascal :
  forall n i:nat, (i < n)%nat -> C n i + C n (S i) = C (S n) (S i).
Proof.
Admitted.

  (*********************)
  (*********************)
Lemma binomial :
  forall (x y:R) (n:nat),
    (x + y) ^ n = sum_f_R0 (fun i:nat => C n i * x ^ i * y ^ (n - i)) n.
Proof.
Admitted.
