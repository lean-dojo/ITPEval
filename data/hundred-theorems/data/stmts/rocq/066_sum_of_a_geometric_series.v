(* Copyright © 1998-2006
 * Henk Barendregt
 * Luís Cruz-Filipe
 * Herman Geuvers
 * Mariusz Giero
 * Rik van Ginneken
 * Dimitri Hendriks
 * Sébastien Hinderer
 * Bart Kirkels
 * Pierre Letouzey
 * Iris Loeb
 * Lionel Mamane
 * Milad Niqui
 * Russell O’Connor
 * Randy Pollack
 * Nickolay V. Shmyrev
 * Bas Spitters
 * Dan Synek
 * Freek Wiedijk
 * Jan Zwanenburg
 *
 * This work is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This work is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along
 * with this work; if not, write to the Free Software Foundation, Inc.,
 * 51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.
 *)

Require Export CoRN.ftc.FunctSeries.
Require Export CoRN.ftc.MoreFunctions.

(** printing FSeries_Sum %\ensuremath{\sum_{\infty}}% #&sum;'<sub>&infin;</sub># *)

Section Definitions.

(**
* More on Sequences and Series

We will now extend our convergence definitions and results for
sequences and series of functions defined in compact intervals to
arbitrary intervals.

%\begin{convention}% Throughout this file, [J] will be an interval,
[f, g] will be sequences of continuous (in [J]) functions and [F,G]
will be continuous (in [J]) functions.
%\end{convention}%

** Sequences

First we will consider the case of sequences.

*** Definitions

Some of the definitions do not make sense in this more general setting
(for instance, because the norm of a function is no longer defined),
but the ones which do we simply adapt in the usual way.
*)

Variable J : interval.
Variable f : nat -> PartIR.
Variable F : PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contF : Continuous J F.

Definition Cauchy_fun_seq_IR :=  forall a b Hab (Hinc : included (compact a b Hab) J),
  Cauchy_fun_seq _ _ _ f (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc).

Definition conv_fun_seq_IR := forall a b Hab (Hinc : included (Compact Hab) J),
  conv_fun_seq a b Hab f (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc).

Definition conv_fun_seq'_IR := forall a b Hab (Hinc : included (Compact Hab) J),
  conv_fun_seq' a b Hab f F
    (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc)
    (included_imp_Continuous _ _ contF _ _ _ Hinc).

Definition Cauchy_fun_seq2_IR := forall a b Hab (Hinc : included (compact a b Hab) J),
  Cauchy_fun_seq2 _ _ _ f (fun n => included_imp_Continuous _ _ (contf n) _ _ _ Hinc).

(**
The equivalences between these definitions still hold.
*)

Lemma conv_Cauchy_fun_seq'_IR : conv_fun_seq'_IR -> Cauchy_fun_seq_IR.
Proof.
Admitted.

Lemma Cauchy_fun_seq_Lim_char : forall a b Hab (Hinc : included (Compact Hab) J),
 Feq (Compact Hab) Cauchy_fun_seq_Lim_IR
  (Cauchy_fun_seq_Lim _ _ _ _ _ (conv a b Hab Hinc)).
Proof.
Admitted.

Lemma FSeries_Sum_char : forall a b Hab (Hinc : included (Compact Hab) J),
 Feq (Compact Hab) FSeries_Sum (Fun_Series_Sum (H a b Hab Hinc)).
Proof.
Admitted.

End Series_Definitions.

Arguments FSeries_Sum [J f].

Section More_Series_Definitions.

Variable J : interval.
Variable f : nat -> PartIR.

(**
Absolute convergence still exists.
*)

Definition fun_series_abs_convergent_IR :=
 fun_series_convergent_IR J (fun n => FAbs (f n)).

End More_Series_Definitions.

Section Convergence_Results.

(**
As before, any series converges to its sum.
*)

Variable J : interval.
Variable f : nat -> PartIR.

Lemma FSeries_conv : forall (convF : fun_series_convergent_IR J f) H H',
 conv_fun_seq'_IR J (fun n => FSum0 n f) (FSeries_Sum convF) H H'.
Proof.
Admitted.

Lemma convergent_imp_inc : fun_series_convergent_IR J f -> forall n, included J (Dom (f n)).
Proof.
Admitted.

Lemma convergent_imp_Continuous : fun_series_convergent_IR J f -> forall n,
 Continuous J (f n).
Proof.
Admitted.

Lemma Continuous_FSeries_Sum : forall H, Continuous J (FSeries_Sum (J:=J) (f:=f) H).
Proof.
Admitted.

End Convergence_Results.

#[global]
Hint Resolve convergent_imp_inc: included.
#[global]
Hint Resolve convergent_imp_Continuous Continuous_FSeries_Sum: continuous.

Section Operations.

(**
** Algebraic Operations

Convergence is well defined and preserved by operations.
*)

Variable J : interval.

Lemma conv_fun_const_series_IR : forall x : nat -> IR, convergent x ->
 fun_series_convergent_IR J (fun n => [-C-] (x n)).
Proof.
Admitted.

Lemma fun_const_series_Sum_IR : forall y H
 (H' : fun_series_convergent_IR J (fun n => [-C-] (y n))) x Hx, FSeries_Sum H' x Hx [=] series_sum y H.
Proof.
Admitted.

Lemma conv_zero_fun_series_IR : fun_series_convergent_IR J (fun n => [-C-][0]).
Proof.
Admitted.

Lemma FSeries_Sum_zero_IR : forall (H : fun_series_convergent_IR J (fun n => [-C-][0]))
   x Hx, FSeries_Sum H x Hx [=] [0].
Proof.
Admitted.

Variables f g : nat -> PartIR.

Lemma fun_series_convergent_wd_IR : (forall n, Feq J (f n) (g n)) ->
 fun_series_convergent_IR J f -> fun_series_convergent_IR J g.
Proof.
Admitted.

(* begin show *)
Hypothesis convF : fun_series_convergent_IR J f.
Hypothesis convG : fun_series_convergent_IR J g.
(* end show *)

Lemma FSeries_Sum_wd' : (forall n, Feq J (f n) (g n)) -> Feq J (FSeries_Sum convF) (FSeries_Sum convG).
Proof.
Admitted.

Lemma FSeries_Sum_plus_conv : fun_series_convergent_IR J (fun n => f n{+}g n).
Proof.
Admitted.

Lemma FSeries_Sum_plus : forall H : fun_series_convergent_IR J (fun n => f n{+}g n),
 Feq J (FSeries_Sum H) (FSeries_Sum convF{+}FSeries_Sum convG).
Proof.
Admitted.

Lemma FSeries_Sum_inv_conv : fun_series_convergent_IR J (fun n => {--} (f n)).
Proof.
Admitted.

Lemma FSeries_Sum_inv : forall H : fun_series_convergent_IR J (fun n => {--} (f n)),
 Feq J (FSeries_Sum H) {--} (FSeries_Sum convF).
Proof.
Admitted.

Lemma FSeries_Sum_minus_conv : fun_series_convergent_IR J (fun n => f n{-}g n).
Proof.
Admitted.

Lemma FSeries_Sum_minus : forall H : fun_series_convergent_IR J (fun n => f n{-}g n),
 Feq J (FSeries_Sum H) (FSeries_Sum convF{-}FSeries_Sum convG).
Proof.
Admitted.

(**
%\begin{convention}% Let [c:IR] and [H:PartIR] be continuous in [J].
%\end{convention}%
*)

Variable c : IR.
Variable H : PartIR.
Hypothesis contH : Continuous J H.

Lemma FSeries_Sum_scal_conv : fun_series_convergent_IR J (fun n => H{*}f n).
Proof.
Admitted.

Lemma FSeries_Sum_scal : forall H' : fun_series_convergent_IR J (fun n => H{*}f n),
 Feq J (FSeries_Sum H') (H{*}FSeries_Sum convF).
Proof.
Admitted.

End Operations.

Section Convergence_Criteria.

(**
*** Convergence Criteria

The most important tests for convergence of series still apply: the
comparison test (in both versions) and the ratio test.
*)

Variable J : interval.
Variable f : nat -> PartIR.
Hypothesis contF : forall n, Continuous J (f n).

Lemma fun_str_comparison_IR : forall g : nat -> PartIR, fun_series_convergent_IR J g ->
 {k : nat | forall n, k <= n -> forall x, J x -> forall Hx Hx', AbsIR (f n x Hx) [<=] g n x Hx'} ->
 fun_series_convergent_IR J f.
Proof.
Admitted.

Lemma fun_comparison_IR : forall g : nat -> PartIR, fun_series_convergent_IR J g ->
 (forall n x, J x -> forall Hx Hx', AbsIR (f n x Hx) [<=] g n x Hx') ->
 fun_series_convergent_IR J f.
Proof.
Admitted.

Lemma abs_imp_conv_IR : fun_series_abs_convergent_IR J f ->
 fun_series_convergent_IR J f.
Proof.
Admitted.

Lemma fun_ratio_test_conv_IR : {N : nat | {c : IR | c [<] [1] | [0] [<=] c /\ (forall x,
  J x -> forall n, N <= n -> forall Hx Hx', AbsIR (f (S n) x Hx') [<=] c[*]AbsIR (f n x Hx))}} ->
 fun_series_convergent_IR J f.
Proof.
Admitted.

End Convergence_Criteria.

Section Power_Series.

(** ***Power Series

The geometric series converges on the open interval (-1, 1)
*)

Lemma fun_power_series_conv_IR : fun_series_convergent_IR (olor ([--][1]) [1]) (fun (i:nat) => Fid IR{^}i).
Proof.
Admitted.

End Power_Series.

Section Insert_Series.

(**
*** Translation

When working in particular with power series and Taylor series, it is
sometimes useful to ``shift'' all the terms in the series one position
forward, that is, replacing each $f_{i+1}$#f<sub>i+1</sub># with
$f_i$#f<sub>i</sub># and inserting the null function in the first
position.  This does not affect convergence or the sum of the series.
*)

Variable J : interval.
Variable f : nat -> PartIR.
Hypothesis convF : fun_series_convergent_IR J f.

Definition insert_series n : PartIR :=
  match n with
  | O => [-C-][0]
  | S p => f p
  end.

Lemma insert_series_cont : forall n, Continuous J (insert_series n).
Proof.
Admitted.

Lemma insert_series_sum_char : forall n x Hx Hx',
 fun_seq_part_sum f n x Hx [=] fun_seq_part_sum insert_series (S n) x Hx'.
Proof.
Admitted.

Lemma insert_series_conv : fun_series_convergent_IR J insert_series.
Proof.
Admitted.

Lemma insert_series_sum : Feq J (FSeries_Sum convF) (FSeries_Sum insert_series_conv).
Proof.
Admitted.

End Insert_Series.

