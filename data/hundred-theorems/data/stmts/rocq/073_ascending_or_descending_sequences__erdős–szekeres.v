(** * Combi.Erdos_Szekeres.Erdos_Szekeres : The Erdös-Szekeres theorem *)
(******************************************************************************)
(*      Copyright (C) 2014-2018 Florent Hivert <florent.hivert@lri.fr>        *)
(*                                                                            *)
(*  Distributed under the terms of the GNU General Public License (GPL)       *)
(*                                                                            *)
(*    This code is distributed in the hope that it will be useful,            *)
(*    but WITHOUT ANY WARRANTY; without even the implied warranty of          *)
(*    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU       *)
(*    General Public License for more details.                                *)
(*                                                                            *)
(*  The full text of the GPL is available at:                                 *)
(*                                                                            *)
(*                  http://www.gnu.org/licenses/                              *)
(******************************************************************************)
(** * The Erdös-Szekeres theorem on monotonic subsequences.

A proof of the Erdös Szekeres theorem about longest increasing and
decreasing subsequences. The theorem is [Erdos_Szekeres] and
says that any sequence [s] of length at least [n*m+1] over a totally ordered
type contains
- either a nondecreasing subsequence of length [n+1];
- or a strictly decreasing subsequence of length [m+1].
We prove it as a corollary of Greene's theorem on the Robinson-Schensted
correspondance. Note that there are other proof which require less theory.
 *****)
Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrfun ssrbool eqtype ssrnat seq fintype.
From mathcomp Require Import tuple finfun finset bigop path order.

Require Import partition tableau Schensted ordtype Greene Greene_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory.
Open Scope N.

Section OrderedType.

Variables (disp : unit) (T : inhOrderType disp).

Lemma Greene_rel_one (s : seq T) (R : rel T) :
  exists t : seq T, subseq t s /\ sorted R t /\ size t = (Greene_rel R s) 1.
Proof.
Admitted.

Theorem Erdos_Szekeres (m n : nat) (s : seq T) :
  size s > m * n ->
  (exists t, subseq t s /\ sorted <=%O t /\ size t > m) \/
  (exists t, subseq t s /\ sorted >%O t /\ size t > n).
Proof.
Admitted.

End OrderedType.
