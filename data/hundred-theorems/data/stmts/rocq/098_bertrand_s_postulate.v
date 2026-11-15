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


(***********************************************************************
    Proof of Bertrand's conjecture: Bertrand.v
                                         Laurent.Thery@inria.fr (2002)
  *********************************************************************)
From Coq Require Export RIneq.
From Coq Require Import Wf_nat Ranalysis Rtrigo ArithRing Lra.
From Bertrand Require Export Raux PowerBinomial Check128 PrimeDirac.

(** Upper Bound for (binonial 2n n) *)

Theorem upper_bound :
 forall n : nat,
 power 2 7 <= n ->
 (forall p : nat, n < p -> p < 2 * n -> ~ prime p) ->
 binomial (2 * n) n <
 power (2 * n) (div (sqr (2 * n)) 2 - 1) * power 4 (div (2 * n) 3).
Proof.
Admitted.

(** If there is no prime number this inequality should hold *) 
Theorem no_prime_imp_spec_inegality :
 forall n : nat,
 power 2 7 <= n ->
 (forall p : nat, n < p -> p < 2 * n -> ~ prime p) ->
 power 4 n < power (2 * n) (div (sqr (2 * n)) 2) * power 4 (div (2 * n) 3).
Proof.
Admitted.

(** The oppositive inequality holds for x > 128 *) 
Theorem spec_fun_bound :
 forall x : R,
 (Rpower 2 (1 + (1 + (1 + (1 + 3)))) <= x)%R ->
 (Rpower (2 * x) (sqrt (2 * x) / 2) < Rpower (1 + 3) (x / 3))%R.
Proof.
Admitted.

(** Main result: there is always a prime between n and 2n *)
 
Theorem Bertrand :
 forall n : nat, 2 <= n -> exists p : nat, prime p /\ n < p /\ p < 2 * n.
Proof.
Admitted.
