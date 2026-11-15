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
Require Import Lra.

Open Scope R_scope.
(* begin hide *)

Lemma epsilon_2 : forall x, 0 < x -> x / 2 < x.
Proof.
Admitted.

Lemma Rabs_include :
  forall x y u v, x <= u <= y -> x <= v <= y -> Rabs (u - v) <= Rabs (x - y).
Proof.
Admitted.

Lemma Rabs_max : forall x y d, Rabs (x - y) <= d -> x <= y + d.
Proof.
Admitted.

Lemma Rabs_min : forall x y d, Rabs (x - y) <= d -> x - d <= y.
Proof.
Admitted.

Section middle_facts.

Definition middle (x y : R) := (x + y) / 2.

Variables x y x' y': R.

Lemma Rlt_middle_r : x < y -> (middle x y) < y.
Proof.
Admitted.

Lemma Rlt_middle_l : x < y -> x < middle x y.
Proof.
Admitted.

Lemma middle_sym : middle x y = middle y x.
Proof.
Admitted.

Lemma middle_minus : x - (middle x y) = (x - y) / 2.
Proof.
Admitted.

Lemma middle_dist : R_dist x (middle x y) = (R_dist x y) / 2.
Proof.
Admitted.

End middle_facts.

Section succ_facts.

Definition succ x y k :=
  let m := middle x y in
  let loc := total_order_T m k in
  match loc with
  | inleft (left _) => (x, m)
  | inleft (right _) => (x, middle x m)
  | inright _ => (m, y)
  end
.

Variable x y k : R.
Hypothesis H : x < y.

Lemma succ_compat : fst (succ x y k) < snd (succ x y k).
Proof.
Admitted.

Lemma succ_not_in : ~ (fst (succ x y k) <= k <= snd (succ x y k)).
Proof.
Admitted.

Lemma succ_included_l : x <= fst (succ x y k).
Proof.
Admitted.

Lemma succ_included_r : snd (succ x y k) <= y.
Proof.
Admitted.

Lemma succ_dist : R_dist (fst (succ x y k)) (snd (succ x y k)) <= (R_dist x y) / 2.
Proof.
Admitted.

End succ_facts.

Section CantorDiagonal.

Variable lb ub : R.
Hypothesis not_empty : lb < ub. 
Variable f : nat -> R.

Definition Rn n := f n.

Fixpoint Dn n {struct n} :=
  match n with
  | O => succ lb ub (Rn O)
  | S m =>
    succ (fst (Dn m)) (snd (Dn m)) (Rn n)
  end
.

Lemma non_zero_dist : R_dist lb ub > 0.
Proof.
Admitted.

Lemma diagonal_compat : forall n, fst (Dn n) < snd (Dn n).
Proof.
Admitted.

Lemma diagonal_included_l : forall n p, (n <= p)%nat -> fst (Dn n) <= fst (Dn p).
Proof.
Admitted.

Lemma diagonal_included_r : forall n p, (n <= p)%nat -> snd (Dn p) <= snd (Dn n).
Proof.
Admitted.

Lemma diagonal_dist : forall n, R_dist (fst (Dn n)) (snd (Dn n)) <= (R_dist lb ub) * ((/2) ^ (S n)).
Proof.
Admitted.

Lemma diagonal_not_in : forall n p, (n <= p)%nat -> ~ (fst (Dn p) <= Rn n <= snd (Dn p)).
Proof.
Admitted.

Definition Ln n := middle (fst (Dn n)) (snd (Dn n)).

Lemma sequence_bound : forall n p, (n <= p)%nat -> (fst (Dn n)) <= Ln p <= (snd (Dn n)).
Proof.
Admitted.

Lemma sequence_cauchy : forall n p q, (p >= n)%nat -> (q >= n)%nat -> R_dist (Ln p) (Ln q) < (R_dist lb ub) * (/2) ^ n.
Proof.
Admitted.

Lemma sequence_cauchy_crit : Cauchy_crit Ln.
Proof.
Admitted.

Lemma sequence_cv : { l : R | Un_cv Ln l }.
Proof.
Admitted.

Definition l := proj1_sig sequence_cv.
Definition l_is_limit := proj2_sig sequence_cv.

Lemma l_in_Dn : forall n, fst (Dn n) <= l <= snd (Dn n).
Proof.
Admitted.

Lemma l_not_in_Rn : forall n, ~(Rn n = l).
Proof.
Admitted.

Lemma l_in_segment : lb <= l <= ub.
Proof.
Admitted.

Lemma segment_uncountable : { l | forall n, l <> Rn n }.
Proof.
Admitted.

End CantorDiagonal.
(* end hide *)

(** * R is uncountable. *)

Theorem R_uncountable_strong :
  forall (f : nat -> R) (x y : R), x < y -> {l : R | forall n, l <> f n & x <= l <= y}.
Proof.
Admitted.

Theorem R_uncountable : forall (f : nat -> R), {l : R | forall n, l <> f n}.
Proof.
Admitted.
