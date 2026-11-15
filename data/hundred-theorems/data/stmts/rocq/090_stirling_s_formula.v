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


(** Proof of Stirling equivalence of factorial. *)

Require Import Reals.
Require Import Rsequence_facts.
Require Import Rseries_def.
Require Import Rseries_facts.
Require Import Rseries_usual.
Require Import Rpser.
Require Import Rintegral.
Require Import RTaylor.
Require Import Lia.
Require Import Lra.
Require Import Wallis.
Open Scope R_scope.

(** printing ~	~ *)
(** Partial result : De Moivre approximation. *)

Section De_Moivre.
(* begin hide *)

Let Un n := (INR n) ^ n * exp (- (INR n)) * sqrt (INR n) / Rseq_fact n.

Let Vn n :=
match n with
| 0 => 0
| _ => ln (Un (S n) / Un n)
end.

Hint Resolve lt_0_INR : stirling.
Hint Resolve sqrt_lt_R0 : stirling.
Hint Resolve exp_pos : stirling.
Hint Resolve lt_O_fact : stirling.
Hint Resolve pow_lt : stirling.
Hint Resolve Rmult_lt_0_compat : stirling.
Hint Resolve Rinv_0_lt_compat : stirling.
Hint Resolve Rgt_not_eq : stirling.

Lemma Vn_O : Vn 0 = 0.
Proof.
Admitted.

Lemma Vn_S : forall n, (0 < n)%nat -> Vn n = ln (Un (S n) / Un n).
Proof.
Admitted.

Lemma ln_pow : forall r n, 0 < r -> ln (r ^ n) = INR n * ln r.
Proof.
Admitted.

Lemma ln_sqrt : forall r, 0 < r -> ln (sqrt r) = ln r / 2.
Proof.
Admitted.

Lemma Un_pos : forall n, (0 < n)%nat -> 0 < Un n.
Proof.
Admitted.

Lemma Vn_simpl :
  forall n, (0 < n)%nat -> Vn n = (INR n + / 2) * ln (1 + / INR n) - 1.
Proof.
Admitted.

Let Tn n :=
match n with
| 0 => 0 
| _ => (- 1) ^ (S n) / (INR n)
end.

Let Rn n := (/ INR n + - / 2 * (/ INR n) ^ 2 + / 3 * (/ INR n) ^ 3).

Let Sn n := ln (1 + / INR n) - Rn n.

Let Qn d n := Rseq_inv_poly d n.

Lemma Qn_S : forall d n, (0 < n)%nat -> Qn d n = (/ INR n) ^ d.
Proof.
Admitted.
Lemma ln_taylor_3 : Sn = O(Qn 4).
Proof.
Admitted.

Lemma Vn_maj : Vn = O(Qn 2).
Proof.
Admitted.

Lemma Rser_cv_Riemann : {l | Rser_abs_cv (Qn 2) l}.
Proof.
Admitted.

Lemma Rser_cv_Vn : {l | Rser_cv Vn l}.
Proof.
Admitted.


Lemma Vn_ser_eq : forall n, sum_f_R0 Vn n = ln (Un (S n)) - ln (Un 1).
Proof.
Admitted.

Lemma Un_cv : {l | Rseq_cv Un l & 0 < l}.
Proof.
Admitted.

(* end hide *)

Lemma De_Moivre_equiv : {C | Rseq_fact ~ (fun n => C * (INR n) ^ n * exp (- (INR n)) * sqrt (INR n)) & 0 < C}.
Proof.
Admitted.

End De_Moivre.
(* begin hide *)

Lemma exp_pow x n : (exp x) ^ n = exp (x* (INR n)).
Proof.
Admitted.
(* end hide *)

(** Final result : Stirling approximation. *)

Section Stirling.

Local Coercion INR : nat >-> R.

Lemma Stirling_equiv : Rseq_fact ~ (fun n => sqrt (2 * PI) * (INR n) ^ n * exp (- (INR n)) * sqrt (INR n)).
Proof.
Admitted.

End Stirling.
