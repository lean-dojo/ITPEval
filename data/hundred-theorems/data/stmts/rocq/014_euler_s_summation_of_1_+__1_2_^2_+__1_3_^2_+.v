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
Require Import Rsequence_facts.
Require Export Rseries.
Require Import Rsequence_subsequence.
Require Import Rtactic.
Require Import Lia.

Open Scope R_scope.

(* begin hide *)
Ltac solve_with_eq a b := let H := fresh in 
 assert (H : a = b); [ | rewrite H; try reflexivity].

Ltac inject := match goal with |- ?a = ?b => recinject (a = b) end
with recinject t := match t with
  | ?a = ?a => idtac
  | ?a ?b = ?a ?c => recinject (b = c)
  | ?b ?a = ?c ?a => recinject (b = c)
  | ?b = ?c => solve_with_eq b c
end.
(* end hide *)

(* Better S_INR *)
Lemma plus_1_S : forall a, INR (S a) = 1 + (INR a).
Proof.
Admitted.

(** * Convergence of the 1/n² series *)

Definition Rseq_square_inv n := / (INR n) ^ 2.
Definition Rseq_square_inv_s n := / (INR (S n)) ^ 2.

(** * Splitting series in odd and even terms *)

Definition odds Un : Rseq := fun n => Un (S (2 * n)).
Definition evens Un : Rseq := fun n => Un (mult 2 n).

(** Convergence of splitting *)
Lemma Rser_cv_pair_compat : forall Un l, Rser_cv Un l -> Rser_cv (fun n => Un (mult 2 n) + Un (S (mult 2 n))) l.
Proof.
Admitted.

(** Finite sum splitting *)

Lemma sum_odd_even_split : forall an n, sum_f_R0 (odds an) n =
  sum_f_R0 an (S (2 * n)) - sum_f_R0 (evens an) n.
Proof.
Admitted.

(** Substracting odd terms *)

Lemma remove_odds : forall Un l, {lu | Rser_cv Un lu} ->
  Rser_cv (evens Un) l -> Rser_cv (Un - (odds Un)) l.
Proof.
Admitted.

(** Substracting even terms *)

Lemma remove_evens : forall Un l, {lu | Rser_cv Un lu} ->
  Rser_cv (odds Un) l -> Rser_cv (Un - evens Un) l.
Proof.
Admitted.

(** * Introduction of pi *)

Definition antg : nat -> R := fun n => (- 1)^n / (2 * (INR n) + 1).
Definition antg_neg : nat -> R := fun n => (- 1)^n / (- 2 * (INR n) + 1).

Lemma PI_tg_PI : Rseq_cv (sum_f_R0 (tg_alt PI_tg)) (PI / 4).
Proof.
Admitted.

Lemma Sum_antg : Rser_cv antg (PI / 4).
Proof.
Admitted.

Lemma antg_shift_neg_compat : Rseq_shift antg_neg == antg.
Proof.
Admitted.

Lemma Sum_antg_neg : Rser_cv antg_neg (PI / 4 + 1).
Proof.
Admitted.

Definition bntg n := / (2 * (INR n) + 1) ^ 2.
Definition bntg_neg n := / (- 2 * (INR n) + 1) ^ 2.

Lemma bntg_pos : forall n, 0 < bntg n.
Proof.
Admitted.

Lemma odd_not_zero : forall n, 2 * (INR n) + 1 <> 0.
Proof.
Admitted.

Lemma neg_odd_not_zero : forall n, 2 * (INR n) - 1 <> 0.
Proof.
Admitted.

Lemma bntg_neg_simpl : forall n, 
  1 / (- 2 * (INR n) + 1) ^ 2 = 1 / (2 * (INR n) - 1) ^ 2.
Proof.
Admitted.

Definition pi_tg2 (n : nat) := 2 / ((4 * (INR n) + 1) * (4 * (INR n) + 3)).

Lemma pi_tg2_corresp : forall n, 
  pi_tg2 n = tg_alt PI_tg (2 * n) + tg_alt PI_tg (S (2 * n)).
Proof.
Admitted.

Lemma pi_tg2_cv : { l | Rser_cv pi_tg2 l }.
Proof.
Admitted.

Lemma Rser_cv_bntg : {l | Rser_cv bntg l}.
Proof.
Admitted.

(** * Sums indexed by relative integers (from -N to N) *)

Require Import ZArith.

Fixpoint bisum (f : Z -> R) (N : nat) := match N with
  | O => f Z0
  | S n => (bisum f n) + f (Z_of_nat N) + f (- Z_of_nat N)%Z
end.

(** - 1 to a relative integer Z *)

Definition pow1_P p := match p with xO _ => 1 | _ => -1 end.

Definition pow1 z := match z with
  | Z0 => 1
  | Zpos n | Zneg n => pow1_P n
end.

Lemma pow1_P_ind : forall p, pow1_P (Pos.
Proof.
Admitted.

Lemma nat_ind2 : forall (P : nat -> Prop), 
  P O -> P (S O) -> (forall m, P m -> P (S (S m))) -> forall n, P n.
Proof.
Admitted.

Lemma pow1_nat : forall n, pow1 (Z_of_nat n) = (- 1) ^ n.
Proof.
Admitted.

Lemma pow1_nat_neg : forall n, pow1 (- Z_of_nat n) = (- 1) ^ n.
Proof.
Admitted.

Lemma pow1_squared : forall z, (pow1 z) ^ 2 = 1.
Proof.
Admitted.

Lemma pow1_Rabs : forall z, Rabs (pow1 z) = 1.
Proof.
Admitted.

Lemma pow1_P_plus : forall a b, pow1_P (a + b) = pow1_P a * pow1_P b.
Proof.
Admitted.

Lemma pow1_succ : forall z, pow1 (Z.
Proof.
Admitted.

Lemma pow1_plus_nat : forall a b, pow1 (a + Z_of_nat b) = (pow1 a) * (-1) ^ b.
Proof.
Admitted.

(** Operations on bisums *)

Definition zr (op : R -> R) (f : Z -> R) z := op (f z).
Definition zr2 (op : R -> R -> R) (f g : Z -> R) z := op (f z) (g z).
Definition zr22 (op : R -> R -> R) (f g : Z -> Z -> R) x y := op (f x y) (g x y).

Lemma bisum_eq_compat : forall f g n, (forall z, f z = g z) -> bisum f n = bisum g n.
Proof.
Admitted.

Lemma bisum_plus : forall f g n, bisum (zr2 Rplus f g) n = bisum f n + bisum g n.
Proof.
Admitted.

Lemma bisum_minus : forall f g n, bisum (zr2 Rminus f g) n = bisum f n - bisum g n.
Proof.
Admitted.

Lemma bisum_scal_mult : forall f a n, bisum (zr (Rmult a) f) n = a * (bisum f n).
Proof.
Admitted.

Lemma bisum_mult : forall f g n m, (bisum f n) * (bisum g m) = 
  bisum (fun i => bisum (fun j => f i * g j) m) n.
Proof.
Admitted.

(** Reversing terms *)

Lemma bisum_reverse : forall f n, bisum f n = bisum (fun i => f (- i)%Z) n.
Proof.
Admitted.

(** Rewriting a bisum as sums *)

Lemma sum_bisum : forall n f, bisum f (S n) =
  sum_f_R0 (fun i => f (Z_of_nat i)) (S n) + sum_f_R0 (fun i => f (- Z_of_nat (S i))%Z) n.
Proof.
Admitted.

(** * Introducing pi to bisums *)

Definition anz z := (pow1 z) / (2 * (IZR z) + 1).
Definition bnz z := / (2 * (IZR z) + 1) ^ 2.
Definition An := bisum anz.
Definition Bn := bisum bnz.

Lemma anz_antg : forall n, antg n = anz (Z_of_nat n).
Proof.
Admitted.

Lemma anz_antg_neg : forall n, antg_neg n = anz (- Z_of_nat n).
Proof.
Admitted.

Lemma bisum_anz_antg : (sum_f_R0 antg + (sum_f_R0 antg_neg - 1))%Rseq == bisum anz.
Proof.
Admitted.

Lemma An_cv : Rseq_cv An (PI / 2).
Proof.
Admitted.

Lemma An_squared_cv : Rseq_cv (An * An) (PI ^ 2 / 4).
Proof.
Admitted.

(** * Double sums *)

Definition bisumsum f N := bisum (fun i => (bisum (f i) N)) N.

(** Double sum minus its diagonal *)

Definition bisum_strip f j N := bisum f N - (f j).
Definition bisumsum_strip_diag f N := bisumsum f N - bisum (fun i => (f i i)) N.

(** Double sum in which its diagonal terms are null *)

Definition bisum_strip' f j N := bisum (fun i => if Z.eq_dec i j then 0 else f i) N.
Definition bisumsum_strip_diag' f N := bisumsum (fun i j => if Z.eq_dec i j then 0 else f i j) N.

(** Weak extensional equality *)

Lemma bisumsum_eq_compat : forall f g n, (forall x y, f x y = g x y) ->
  bisumsum f n = bisumsum g n.
Proof.
Admitted.

(** Bounded extensional equality *)

Lemma bisum_eq_compat_bounded : forall f g n, (forall z, ((-Z_of_nat n) <= z <= Z_of_nat n)%Z -> f z = g z) ->
  bisum f n = bisum g n.
Proof.
Admitted.

(** Double sum distributivity *)

Lemma bisumsum_square : forall f n, bisumsum (fun i j => f i * f j) n = bisum f n * bisum f n.
Proof.
Admitted.

(** Inequalities *)

Lemma Psucc_lt : forall p, (Zpos p < Zpos (Pos.
Proof.
Admitted.

Lemma Psucc_lt_neg : forall p, (Zneg (Pos.
Proof.
Admitted.

(** A special term outside the bounds can be ignored *)

Lemma bisum_not_in : forall f g j n, (j < (- Z_of_nat n) \/ Z_of_nat n < j)%Z -> 
  bisum (fun i : Z => if Z.
Proof.
Admitted.

(** A special term between the bounds can be extracted *)

Lemma bisum_in : forall f g j n, (- Z_of_nat n <= j <= Z_of_nat n)%Z -> 
  bisum (fun i : Z => if Z.
Proof.
Admitted.

(** Stripping terms *)

Definition Zzero : Z -> R := fun _ => 0.

Lemma bisum_strip_equiv : forall f n j, ((- Z_of_nat n) <= j <= Z_of_nat n)%Z -> 
  bisum_strip f j n = bisum_strip' f j n.
Proof.
Admitted.

Lemma bisum_strip_nothing : forall f n j, ((- Z_of_nat (S n)) = j \/ j = Z_of_nat (S n))%Z -> 
  bisum_strip' f j n = bisum f n.
Proof.
Admitted.

(** Steps of calculus in bisums *)

Lemma bisum_one_step : forall f n, bisum f (S n) = bisum f n + f (Z_of_nat (S n)) + f (- Z_of_nat (S n))%Z.
Proof.
Admitted.

Lemma bisumsum_one_step : forall f n m, 
  bisum (fun i => bisum (f i) (S n)) m =
  bisum (fun i => bisum (f i) n) m + 
  bisum (fun i =>        f i (Z_of_nat (S n))    ) m +
  bisum (fun i =>        f i (- Z_of_nat (S n))%Z ) m.
Proof.
Admitted.

(** Switching indices *)

Lemma bisum_eq_sym : forall f z n,
  bisum (fun i : Z => if Z.
Proof.
Admitted.

(** Substracting the diagonal terms sum makes them null in the main double sum *)

Lemma strip_diag : forall f n, bisumsum_strip_diag' f n = bisumsum_strip_diag f n.
Proof.
Admitted.

(** * Rewriting double sums *)

(** Switching indices in a double sum *)

Lemma bisumsum_switch_index : forall f n, bisumsum (fun i j => f j i) n = bisumsum f n.
Proof.
Admitted.

(** Switching indices in a double sum (where diagonal terms are null) *)

Lemma bisumsum_strip_diag'_switch_index : forall f n,
  bisumsum_strip_diag' (fun i j => f j i) n =
  bisumsum_strip_diag' f n.
Proof.
Admitted.

(** Adding double sums *)

Lemma bisumsum_strip_diag'_plus : forall f g n,
  bisumsum_strip_diag' (fun i j => f i j + g i j) n =
  bisumsum_strip_diag' f n +
  bisumsum_strip_diag' g n.
Proof.
Admitted.

(** Switching indices of only one term in a sum in a double sum *)

Lemma bisumsum_plus_switch : forall f g n,
  bisumsum_strip_diag' (fun i j => f i j + g i j) n =
  bisumsum_strip_diag' (fun i j => f i j + g j i) n.
Proof.
Admitted.

(** Extensional equality but on the diagonal terms *)

Lemma bisumsum_strip_diag'_eq_but_diag_compat : forall f g n,
  (forall i j, i <> j -> f i j = g i j) ->
  bisumsum_strip_diag' f n = bisumsum_strip_diag' g n.
Proof.
Admitted.

(** Shifting a sequence (with an integer) *)
Fixpoint sum1 u n := match n with
  | O => 0
  | S n' => (sum1 u n') + u (Z_of_nat n)
end.

Lemma sum_f_R0_sum1 : forall u n, sum1 u (S n) = 
  sum_f_R0 (fun i => u (Z_of_nat (S i))) n.
Proof.
Admitted.

Definition shiftp (u:Z->R) (p:nat) (i:Z) := u (i + (Z_of_nat p))%Z.

Lemma bisum_shifting_S : forall u a b, 
  bisum (shiftp u (S b)) (S a) = 
  bisum (shiftp u b) a +
  u (Z_of_nat (S (a + b))) +
  u (Z_of_nat (S (S (a + b))))
.
Proof.
Admitted.

Lemma bisum_shifting : forall u n p, 
  bisum (shiftp u p) (n + p) = 
  bisum u n + sum1 (shiftp u n) (2 * p)
.
Proof.
Admitted.

(** * Rewriting An * An - Bn *)

Definition d x := 2 * x + 1.
Definition d' z := d (IZR z).

Lemma splitmn : forall n m, d n <> 0 -> d m <> 0 -> m <> n -> 
  / ((d n) * (d m)) = / (2 * (m - n)) * (/ (d n) - / (d m)).
Proof.
Admitted.

Lemma d_not_null : forall z, d' z <> 0.
Proof.
Admitted.

Lemma calc1 : forall N, (An N) * (An N) - Bn N =
  bisumsum_strip_diag' (fun n m =>
    (pow1 m * pow1 n) * / (2 * (IZR (m - n))) * (/ (d' n) - / (d' m))
  ) N.
Proof.
Admitted.

Lemma calc2 : forall N, (An N) * (An N) - Bn N = bisumsum_strip_diag'  (fun n m =>
    (pow1 m * pow1 n) * / ((IZR (m - n)) * (d' n))
  ) N.
Proof.
Admitted.

Definition cn n N := bisum (fun m => if Z.eq_dec n m then 0 else pow1 m / (IZR (m - n))) N.

Lemma calc3 : forall N, (An N) * (An N) - Bn N = bisum (fun n => pow1 n / (d' n) * (cn n N)) N.
Proof.
Admitted.

Lemma cn_odd : forall n N, cn (- n)%Z N = - (cn n N).
Proof.
Admitted.

Lemma cn_zero_zero : forall N, cn 0 N = 0.
Proof.
Admitted.

(** * Bounding *)

Lemma cn_pos : forall n N, (S n <= N)%nat ->
  cn (Zpos (P_of_succ_nat n)) N = 
  (pow (-1) (S (S n))) * 
  (sum_f_R0 (fun j => pow (-1) (j + N - n) * / (INR (j + N - n)))) (S (2 * n))
.
Proof.
Admitted.

Lemma alt_bounding : 
  forall u : nat -> R,
  Un_decreasing u ->
  (forall n, 0 <= u n) ->
  forall n, 0 <= sum_f_R0 (tg_alt u) n <= u O.
Proof.
Admitted.

Lemma cn_maj : forall n N, (n <= N)%nat -> Rabs (cn (Z_of_nat n) N) <= / (INR (N - n + 1)).
Proof.
Admitted.

Lemma abound_eq : forall n N, (O <= n)%nat -> (S n <= N)%nat ->
  / (INR (N - n)) * (/ (INR (2 * n + 1)) + / (INR (2 * n + 3))) =
  / (INR (2 * N + 1)) * (2 / (INR (2 * n + 1)) + / (INR (N - n))) +
  / (INR (2 * N + 3)) * (2 / (INR (2 * n + 3)) + / (INR (N - n))).
Proof.
Admitted.

Definition abound N := sum_f_R0 (fun n => / (INR (N - (S n) + 1)) * 
    (/ (INR (2 * n + 1)) + / (INR (2 * n + 3)))
  ) (pred N).

Definition bound1 N :=  / (INR (2 * N + 1)) * 
  sum_f_R0 (fun n => 
    2 / (INR (2 * n + 1)) + / (INR (N - (S n) + 1))
  ) (pred N).

Definition bound2 N :=  / (INR (2 * N + 3)) * 
  sum_f_R0 (fun n => 
    2 / (INR (2 * n + 3)) + / (INR (N - (S n) + 1))
  ) (pred N).

Definition bound1' N :=  / INR (2 * N + 1) * sum_f_R0 (fun n =>  2 / INR (2 * n + 1)) (pred N).
Definition bound2' N :=  / INR (2 * N + 3) * sum_f_R0 (fun n =>  2 / INR (2 * n + 3)) (pred N).
Definition bound1c N :=  / INR (2 * N + 1) * sum_f_R0 (fun n => / INR (N - (S n) + 1)) (pred N).
Definition bound2c N :=  / INR (2 * N + 3) * sum_f_R0 (fun n => / INR (N - (S n) + 1)) (pred N).

Lemma An_squared_Bn_maj : forall N, (1 <= N)%nat -> Rabs (An N * An N - Bn N) <= abound N.
Proof.
Admitted.

Lemma bound_eq : forall N, abound (S N) = bound1 (S N) + bound2 (S N).
Proof.
Admitted.

(** Convergence of the bounds *)

Definition inverse_mean n := sum_f_R0 (fun i => / INR (S i)) n / INR (S n).

Lemma inverse_cv_0 : Rseq_cv (fun i => / INR (S i)) 0.
Proof.
Admitted.

Lemma inverse_mean_cv_0 : Rseq_cv inverse_mean 0.
Proof.
Admitted.

Lemma Rseq_cv_0_pos_maj_compat : forall Un Vn, (forall n, 0 <= Un n) -> (forall n, Un n <= Vn n) ->
  Rseq_cv Vn 0 -> Rseq_cv Un 0.
Proof.
Admitted.

Lemma half_mean_0 : forall Un k m, 0 <= k -> (1 <= m)%nat -> (forall n, 0 <= Un n) -> (forall n, Un n <= k / INR (S n)) ->
  Rseq_cv (fun N => / INR (2 * N + m) * sum_f_R0 Un (pred N)) 0.
Proof.
Admitted.

Lemma bound1'_cv : Rseq_cv bound1' 0.
Proof.
Admitted.

Lemma bound2'_cv : Rseq_cv bound2' 0.
Proof.
Admitted.

Lemma Rsum_switch_index : forall Un N, sum_f_R0 (fun n => Un (N - n)%nat) N = sum_f_R0 Un N.
Proof.
Admitted.

Lemma bound1c_cv : Rseq_cv bound1c 0.
Proof.
Admitted.

Lemma bound2c_cv : Rseq_cv bound2c 0.
Proof.
Admitted.

Lemma bound1_cv : Rseq_cv bound1 0.
Proof.
Admitted.

Lemma bound2_cv : Rseq_cv bound2 0.
Proof.
Admitted.

Lemma abound_cv : Rseq_cv abound 0.
Proof.
Admitted.

(** Final result about sums *)

Lemma An_squared_Bn_cv : Rseq_cv (An * An - Bn) 0.
Proof.
Admitted.

(** * Bn converges to pi²/4 *)

Lemma Bn_cv : Rseq_cv Bn (PI ^ 2 / 4).
Proof.
Admitted.

(** * Linking sums on nat and sums on Z *)

Lemma bnz_bntg : forall n, bntg n = bnz (Z_of_nat n).
Proof.
Admitted.

Lemma bnz_bntg_neg : forall n, bntg_neg n = bnz (- Z_of_nat n).
Proof.
Admitted.

Lemma bisum_bnz_bntg : (sum_f_R0 bntg + (sum_f_R0 bntg_neg - 1))%Rseq == bisum bnz.
Proof.
Admitted.

Definition sumbntg := let (l, _) := Rser_cv_bntg in l.

Lemma Sum_bntg : Rser_cv bntg sumbntg.
Proof.
Admitted.

Lemma bntg_shift_neg_compat : Rseq_shift bntg_neg == bntg.
Proof.
Admitted.

Lemma Sum_bntg_neg : Rser_cv bntg_neg (sumbntg + 1).
Proof.
Admitted.

Lemma Sum_bnz : Rseq_cv Bn (2 * sumbntg).
Proof.
Admitted.

Lemma sumbntg_val : sumbntg = PI ^ 2 / 8.
Proof.
Admitted.

Lemma odd_zeta : Rser_cv bntg (PI ^ 2 / 8).
Proof.
Admitted.

(** * Linking even terms of the 1/n² series to the series itself *)

Lemma odd_zeta_evens : Rser_cv (evens (Rseq_shift Rseq_square_inv)) (PI ^ 2 / 8).
Proof.
Admitted.

Definition zeta2 := let (l, _) := Rser_cv_square_inv in l.

Lemma zeta2_half : Rser_cv (odds (Rseq_shift (Rseq_square_inv))) (zeta2 / 4).
Proof.
Admitted.

(** Final result with free variables *)

Lemma zeta2_val : zeta2 = PI ^ 2 / 6.
Proof.
Admitted.

Coercion INR : nat >-> R.

(** * Final theorem *)

Theorem zeta2_pi_2_6 : Rser_cv (fun n => 1 / (n + 1) ^ 2) (PI ^ 2 / 6).
Proof.
Admitted.
