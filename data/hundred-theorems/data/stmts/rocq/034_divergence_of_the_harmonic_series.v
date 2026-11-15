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

(** Properties involving series and integrals *)
Require Import Reals.
Require Import Rseries_def.
Require Import Rseries_facts.
Require Import RiemannInt.
Require Import Lra.
Require Import Rsequence_facts.
Require Import Rsequence_subsequence.
Require Import Riemann_integrable.
Require Import Rintegral.

Local Open Scope R_scope.
(** printing ~	~ *)
Section Rseries_RiemannInt.

Local Coercion INR : nat >-> R.

(* begin hide *)
Lemma Rle_minus' : forall a b, b <= a -> 0 <= a - b.
Proof.
Admitted.
Lemma Rminus_le_compat_r: forall r r1 r2 : R, r2 <= r1 -> r - r1 <= r - r2.
Proof.
Admitted.
(* end hide *)

Lemma Telescoping_series : forall a n, sum_f_R0 (fun i => a (S i) - a i) n = a (S n) - a O.
Proof.
Admitted.

Lemma Telescoping_series_opp : forall a n, sum_f_R0 (fun i => a i - a (S i)) n = a O - a (S n).
Proof.
Admitted.


(** * Generalized Chasles relation *)
Lemma Rint_generalized_Chasles : forall f An, 
  (forall n : nat, Rint f n (S n) (An n)) -> 
    forall n : nat, Rint f 0 (S n) (sum_f_R0 An n).
Proof.
Admitted.

Section Rser_RiemannInt_link.

Variable f : R -> R.
Hypothesis Hcont : forall x, 0 <= x -> continuity_pt f x.
Hypothesis Hpos : forall x, 0 <= x -> 0 <= f x.
Hypothesis Hdec : forall x y : R, 0 <= x <= y -> f y <= f x.

Lemma Riemann_integrable_f_n_Sn : forall (n : nat), Riemann_integrable f (INR n) (INR (S n)).
Proof.
Admitted.

Lemma Rser_RiemannInt_link_general_term_integrable : forall (n : nat), 
  Riemann_integrable (fun x => fct_cte (f (INR n)) x - f x) (INR n) (INR (S n)).
Proof.
Admitted.

Lemma Rser_RiemannInt_link_general_term_bound (n : nat) : 
  RiemannInt (Rser_RiemannInt_link_general_term_integrable n) <= f (INR n) - f (INR (S n)).
Proof.
Admitted.

(**  * Link between series and integral *)
Lemma Rser_RiemannInt_link : { l | Rser_cv (fun n => f (INR n) - RiemannInt (Riemann_integrable_f_n_Sn n) ) l}.
Proof.
Admitted.

Lemma Rser_RiemannInt_cv_pos_infty : 
    exists pr : forall (n : nat), Riemann_integrable f 0 (INR n), 
    Rseq_cv_pos_infty (fun n => RiemannInt (pr (S n))) ->
        (sum_f_R0 (fun n => f (INR n))) ~ (fun n => RiemannInt (pr (S n))).
Proof.
Admitted.

End Rser_RiemannInt_link.

Section Applications.

Definition ln1 := comp ln (fun x => x+1).

Lemma Rint_inv1 : forall a b, 
  -1 < a <= b -> Rint (/(id + fct_cte 1))%F a b (ln (b + 1) - ln (a + 1)).
Proof.
Admitted.   
      
(** Equivalent of the harmonic series *)
Lemma harmonic_series_equiv : (sum_f_R0 (fun n => / (S n))) ~ (fun n => ln (S (S n))).
Proof.
Admitted.


End Applications.

End Rseries_RiemannInt.
