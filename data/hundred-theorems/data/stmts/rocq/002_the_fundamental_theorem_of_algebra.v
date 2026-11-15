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

Require Export CoRN.fta.CPoly_Rev.
Require Export CoRN.fta.FTAreg.
Import CRing_Homomorphisms.coercions.

(**
* Fundamental Theorem of Algebra
%\begin{convention}% Let [n:nat] and [f] be a complex polynomial of
degree [(S n)].
%\end{convention}%
*)

Section FTA_reg'.

Variable f : cpoly_cring CC.
Variable n : nat.
Hypothesis f_degree : degree (S n) f.

Lemma FTA_reg' :
  {f1 : CCX |
    degree 1 f1 |
    {f2 : CCX | degree n f2 | f [=] f1[*]f2}}.
Proof.
Admitted.

End FTA_reg'.

(**
%\begin{convention}% Let [n:nat], [f] be a complex polynomial of degree
less than or equal to [(S n)] and [c] be a complex number such that
[f!c  [#]  [0]].
%\end{convention}%
*)

Section FTA_1.

Variable f : cpoly_cring CC.
Variable n : nat.
Hypothesis f_degree : degree_le (S n) f.
Variable c : CC.
Hypothesis f_c : f ! c [#] [0].

Lemma FTA_1a : degree_le (S n) (Shift c f).
Proof.
Admitted.

Let g := Rev (S n) (Shift c f).

Lemma FTA_1b : degree (S n) g.
Proof.
Admitted.

Lemma FTA_1 : {f1 : CCX | {f2 : CCX | degree_le 1 f1 /\ degree_le n f2 /\ f [=] f1[*]f2}}.
Proof.
Admitted.

Lemma FTA_1' : {a : CC | {b : CC | {g : CCX | degree_le n g | f [=] (_C_ a[*]_X_[+]_C_ b) [*]g}}}.
Proof.
Admitted.

End FTA_1.

Section Fund_Thm_Alg.

Lemma FTA' : forall n (f : CCX), degree_le n f -> nonConst _ f -> {z : CC | f ! z [=] [0]}.
Proof.
Admitted.

Lemma FTA : forall f : CCX, nonConst _ f -> {z : CC | f ! z [=] [0]}.
Proof.
Admitted.

Lemma FTA_a_la_Henk : forall f : CCX,
 {x : CC | {y : CC | AbsCC (f ! x[-]f ! y) [>][0]}} -> {z : CC | f ! z [=] [0]}.
Proof.
Admitted.

End Fund_Thm_Alg.
