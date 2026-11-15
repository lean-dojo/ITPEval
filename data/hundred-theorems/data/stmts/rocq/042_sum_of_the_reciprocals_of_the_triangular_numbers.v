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


Require Import Reals.
Require Import Rseries_RiemannInt.
Require Import Rseries_facts.
Require Import Rtactic.
Require Import Rsequence_facts.
Require Import Lra.

Definition triangle n := INR (n * S n) / 2.

Lemma triangle_sum n : sum_f_R0 INR n = triangle n.
Proof.
Admitted.

Lemma triangle_non_negative n : 0 <= triangle n.
Proof.
Admitted.

Lemma triangle_positive n : 0 < triangle (S n).
Proof.
Admitted.

Lemma sum_consecutive_triangle n : triangle (S n) + triangle n = INR (S n) * INR (S n).
Proof.
Admitted.

Lemma difference_consecutive_triangle n : (triangle (S n) - triangle n)² = INR (S n) * INR (S n).
Proof.
Admitted.

Lemma sum_triangular_tetrahedral n : sum_f_R0 triangle n = INR (n * S n * S (S n)) / 6.
Proof.
Admitted.

Definition inv_snssn n := / INR (S n * S (S n)).

Definition inv_sn n := / INR (S n).

Lemma diff_inv_snssn n : inv_snssn n = inv_sn n - inv_sn (S n).
Proof.
Admitted.

Lemma sum_inv_snssn n : sum_f_R0 inv_snssn n = 1 - inv_sn (S n).
Proof.
Admitted.

Lemma inv_sn_cv_0 : Rseq_cv inv_sn 0.
Proof.
Admitted.

Lemma ser_cv_inv_snssn : Rser_cv inv_snssn 1.
Proof.
Admitted.

Lemma sum_reciprocal_triangular : Rser_cv (fun n => / triangle (S n)) 2.
Proof.
Admitted.
