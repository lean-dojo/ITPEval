(*
(C) Copyright 2010, COQTAIL team

Project Info: http://sourceforge.net/projects/coqtail/

This library is free software; you can redistribute it and/or modify it
under the terms of the GNU Lesser General Public License as published by
the Free Software Foundation; either version 2.1 of the License, or
(at your option) any later version.

This library is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General Public
License for more details.

You should have received a copy of the GNU Lesser General Public
License along with this library; if not, write to the Free Software
Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301,
USA.
*)

Require Import Lia.
Require Import Rsequence_def.
Require Import Rsequence_facts.
Require Import Rsequence_cv_facts.
Require Import Rsequence_usual_facts.
Require Import Rtactic.
Require Import MyRIneq.

Require Import Cprop_base.
Require Import Csequence.
Require Import Csequence_facts.
Require Import Cpser_def Cpser_base_facts Cpser_facts.
Require Import Cseries.
Require Import Cseries_facts.
Require Import Cdefinitions.
Require Import Canalysis_def.


Open Scope C_scope.

(** * Definition and manipulation of the general term of the power serie of the exponential *)

Definition exp_seq (n : nat) := / INC (fact n).

Lemma exp_seq_neq : forall n : nat, exp_seq n <> 0.
Proof.
Admitted.

Lemma Cdiv_exp_seq_simpl : forall n, (exp_seq (S n)) / (exp_seq n) = / INC (S n).
Proof.
Admitted.

Lemma Deriv_exp_seq_simpl : forall n, An_deriv exp_seq n = exp_seq n.
Proof.
Admitted.

(** * This power serie has a radius of convergence that is infinite *)

Lemma exp_infinite_cv_radius : infinite_cv_radius exp_seq.
Proof.
Admitted.

Definition Cexp (z : C) := sum  _ exp_infinite_cv_radius z.

Definition Deriv_Cexp (z : C) := sum_derive _ exp_infinite_cv_radius z.


(** * The exponential is its own derivative *)

Lemma Cexp_eq_Deriv_Cexp : forall z, Cexp z = Deriv_Cexp z.
Proof.
Admitted.

Lemma derivable_pt_lim_Cexp : forall z, derivable_pt_lim Cexp z (Cexp z).
Proof.
Admitted.

(** ** Euler's Formula*)

Lemma Cexp_exp_compat : forall a : R, Cexp a =  exp a.
Proof.
Admitted.

Lemma Cre_Cpow_2 : forall (a : R) (n : nat), Cre ((0 +i a) ^ (2 * n)) = ((-1) ^ n * a ^ (2*n))%R.
Proof.
Admitted.

Lemma Cim_Cpow_2 : forall (a : R) (n : nat), Cim ((0 +i a) ^ (2 * n)) = R0.
Proof.
Admitted.

Lemma Cre_Cpow_S2 : forall (a : R) (p : nat), Cre ((0 +i  a) ^ S (2 * p)) = R0.
Proof.
Admitted.

Lemma Cim_Cpow_S2 : forall (a : R) (n : nat), Cim ((0 +i a) ^ (S (2 * n))) = ((-1) ^ n * a ^ S (2*n))%R.
Proof.
Admitted.

Lemma Cexp_trigo_compat : forall a, Cexp (0 +i a) = cos a +i sin a.
Proof.
Admitted.

Lemma Cexp_abs_cv : forall z, {l | Cser_abs_cv (gt_pser exp_seq z) l}.
Proof.
Admitted.

Lemma binomial_diag : forall n, Binomial.
Proof.
Admitted.

Lemma binomial_zero : forall n, Binomial.
Proof.
Admitted.

Open Scope C_scope.

Lemma binomial_sum : forall (x y:C) n,
  (x + y) ^ n = sum_f_C0 (fun p => IRC (Binomial.
Proof.
Admitted.

Lemma Cexp_add : forall a b, Cexp (a + b) = (Cexp a * Cexp b)%C.
Proof.
Admitted.

Lemma Cexp_0 : Cexp C0 = C1.
Proof.
Admitted.

Lemma Cexp_mult : forall a n, Cexp (INC n * a) = (Cexp a) ^ n.
Proof.
Admitted.
