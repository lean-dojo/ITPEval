(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)

From Coq Require Import ArithRing.
From Coq Require Import Compare_dec.
From Coq Require Import Wf_nat.
From Coq Require Import Arith.
From Coq Require Import Lia.
 
Theorem minus_minus : forall a b c : nat, a - b - c = a - (b + c).
Proof.
Admitted.
 
Remark expand_mult2 : forall x : nat, 2 * x = x + x.
Proof.
Admitted.
 
Theorem lt_neq : forall x y : nat, x < y -> x <> y.
Proof.
Admitted.

#[local] Hint Resolve lt_neq : core.
 
Theorem monotonic_inverse :
 forall f : nat -> nat,
 (forall x y : nat, x < y -> f x < f y) ->
 forall x y : nat, f x < f y -> x < y.
Proof.
Admitted.
 
Theorem mult_lt : forall a b c : nat, c <> 0 -> a < b -> a * c < b * c.
Proof.
Admitted.
 
Remark add_sub_square_identity :
 forall a b : nat,
 (b + a - b) * (b + a - b) = (b + a) * (b + a) + b * b - 2 * ((b + a) * b).
Proof.
Admitted.
 
Theorem sub_square_identity :
 forall a b : nat, b <= a -> (a - b) * (a - b) = a * a + b * b - 2 * (a * b).
Proof.
Admitted.
 
Theorem square_monotonic : forall x y : nat, x < y -> x * x < y * y.
Proof.
Admitted.
 
Theorem root_monotonic : forall x y : nat, x * x < y * y -> x < y.
Proof.
Admitted.
 
Remark square_recompose : forall x y : nat, x * y * (x * y) = x * x * (y * y).
Proof.
Admitted.
 
Remark mult2_recompose : forall x y : nat, x * (2 * y) = x * 2 * y.
Proof.
Admitted.

Section sqrt2_decrease.

Variables (p q : nat) (pos_q : 0 < q) (hyp_sqrt : p * p = 2 * (q * q)).
 
Theorem sqrt_q_non_zero : 0 <> q * q.
Proof.
Admitted.

#[local] Hint Resolve sqrt_q_non_zero : core.
 
Ltac solve_comparison :=
  apply root_monotonic; repeat rewrite square_recompose; rewrite hyp_sqrt;
   rewrite mult2_recompose; apply mult_lt; auto with arith.
 
Theorem comparison1 : q < p.
Proof.
Admitted.
 
Theorem comparison2 : 2 * p < 3 * q.
Proof.
Admitted.
 
Theorem comparison3 : 4 * q < 3 * p.
Proof.
Admitted.

#[local] Hint Resolve comparison1 comparison2 comparison3: arith.
 
Theorem comparison4 : 3 * q - 2 * p < q.
Proof.
Admitted.
 
Remark mult_minus_distr_l : forall a b c : nat, a * (b - c) = a * b - a * c.
Proof.
Admitted.
 
Remark minus_eq_decompose :
 forall a b c d : nat, a = b -> c = d -> a - c = b - d.
Proof.
Admitted.
 
Theorem new_equality :
 (3 * p - 4 * q) * (3 * p - 4 * q) = 2 * ((3 * q - 2 * p) * (3 * q - 2 * p)).
Proof.
Admitted.

End sqrt2_decrease.

#[local] Hint Resolve Nat.lt_le_incl comparison2: sqrt.
 
Theorem sqrt2_not_rational :
 forall p q : nat, q <> 0 -> p * p = 2 * (q * q) -> False.
Proof.
Admitted.
