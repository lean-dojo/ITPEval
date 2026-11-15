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

Require Export CoRN.ftc.TaylorLemma.

Opaque Min Max N_Deriv.

Section More_Taylor_Defs.

(**
** General case

The generalization to arbitrary intervals just needs a few more definitions.

%\begin{convention}% Let [I] be a proper interval, [F:PartIR] and
[a,b:IR] be points of [I].
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variable F : PartIR.

(* begin show *)
Let deriv_Sn b n Hf :=
 N_Deriv _ pI (S n) F Hf{*} [-C-] ([1][/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]b{-}FId) {^}n.
(* end show *)

Variables a b : IR.
Hypothesis Ha : I a.
Hypothesis Hb : I b.

(* begin show *)
Let fi n Hf i Hi :=
  N_Deriv _ pI _ _ (le_imp_Diffble_n _ _ _ _ (proj1 (Nat.lt_succ_r i n) Hi) F Hf).

Let funct_i n Hf i Hi :=
  [-C-] (fi n Hf i Hi a Ha[/] _[//]nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i.
(* end show *)

Definition Taylor_Seq' n Hf := FSumx _ (funct_i n Hf).

(* begin hide *)
Lemma TaylorB : forall n Hf, Dom (Taylor_Seq' n Hf) b.
Proof.
Admitted.
(* end hide *)

Definition Taylor_Rem n Hf := F b (Diffble_n_imp_inc _ _ _ _ Hf b Hb) [-]
 Taylor_Seq' n Hf b (TaylorB n Hf).

(* begin hide *)
Lemma Taylor_Sumx_lemma : forall n x z y y', (forall H, y 0 H [=] z) ->
  (forall i H H', y' i H' [=] y (S i) H) ->
  x[-]Sumx (G:=IR) (n:=S n) y [=] x[-]z[-]Sumx (G:=IR) (n:=n) y'.
Proof.
Admitted.

Lemma Taylor_lemma_ap : forall n Hf Hf' Ha',
 Taylor_Rem n Hf'[-]deriv_Sn b n Hf a Ha'[*] (b[-]a) [#] [0] -> a [#] b.
Proof.
Admitted.
(* end hide *)

Theorem Taylor' : forall n Hf Hf' e, [0] [<] e -> {c : IR | Compact (Min_leEq_Max a b) c |
 forall Hc, AbsIR (Taylor_Rem n Hf'[-]deriv_Sn b n Hf c Hc[*] (b[-]a)) [<=] e}.
Proof.
Admitted.

End More_Taylor_Defs.

Section Taylor_Theorem.

(**
And finally the ``nice'' version, when we know the expression of the
derivatives of [F].

%\begin{convention}% Let [f] be the sequence of derivatives of [F] of
order up to [n] and [F'] be the nth-derivative of [F].
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variable F : PartIR.

Variable n : nat.
Variable f : forall i : nat, i < S n -> PartIR.

Hypothesis goodF : ext_fun_seq f.
Hypothesis goodF' : ext_fun_seq' f.

Hypothesis derF : forall i Hi, Derivative_n i I pI F (f i Hi).

Variable F' : PartIR.
Hypothesis derF' : Derivative_n (S n) I pI F F'.

Variables a b : IR.
Hypothesis Ha : I a.
Hypothesis Hb : I b.


(* begin show *)
Let funct_i i Hi := let HX := (Derivative_n_imp_inc' _ _ _ _ _ (derF i Hi) a Ha) in
[-C-] (f i Hi a HX [/] _[//] nring_fac_ap_zero _ i) {*} (FId{-} [-C-]a) {^}i.

Definition Taylor_Seq := FSumx _ funct_i.

Let deriv_Sn := F'{*} [-C-] ([1][/] _[//]nring_fac_ap_zero _ n) {*} ( [-C-]b{-}FId) {^}n.
(* end show *)

Lemma Taylor_aux : Dom Taylor_Seq b.
Proof.
Admitted.

Theorem Taylor : forall e, [0] [<] e -> forall Hb', {c : IR | Compact (Min_leEq_Max a b) c |
 forall Hc, AbsIR (F b Hb'[-]Part _ _ Taylor_aux[-]deriv_Sn c Hc[*] (b[-]a)) [<=] e}.
Proof.
Admitted.

End Taylor_Theorem.
