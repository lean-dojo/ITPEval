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

Require Export CoRN.tactics.DiffTactics2.
Require Export CoRN.ftc.MoreFunctions.

Section Rolle.

(**
* Rolle's Theorem

We now begin to work with partial functions.  We begin by stating Rolle's
theorem in the same constructive-real setting as the retained CoRN source.
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.

Variables F F' : PartIR.

Hypothesis derF : Derivative_I Hab' F F'.
Hypothesis Ha : Dom F a.
Hypothesis Hb : Dom F b.
Hypothesis Fab : F a Ha [=] F b Hb.

Variable e : IR.
Hypothesis He : [0] [<] e.

Let contF' : Continuous_I Hab F'.
Proof.
Admitted.

Let derivF :
  forall e : IR,
  [0] [<] e ->
  {d : IR | [0] [<] d |
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy Hx',
  AbsIR (x[-]y) [<=] d ->
  AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x))
    [<=] e[*]AbsIR (y[-]x)}.
Proof.
Admitted.

Let Rolle_lemma2 :
  {d : IR | [0] [<] d |
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy Hx',
  AbsIR (x[-]y) [<=] d ->
  AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e [/]TwoNZ[*]AbsIR (y[-]x)}.
Proof.
Admitted.

Let df := proj1_sig2T _ _ _ Rolle_lemma2.

Let Hdf : [0] [<] df := proj2a_sig2T _ _ _ Rolle_lemma2.

Let Hf :
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy Hx',
  AbsIR (x[-]y) [<=] df ->
  AbsIR (F y Hy[-]F x Hx[-]F' x Hx'[*] (y[-]x)) [<=] e [/]TwoNZ[*]AbsIR (y[-]x) :=
  proj2b_sig2T _ _ _ Rolle_lemma2.

Let Rolle_lemma3 :
  {d : IR | [0] [<] d |
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy, AbsIR (x[-]y) [<=] d -> AbsIR (F' x Hx[-]F' y Hy) [<=] e [/]TwoNZ}.
Proof.
Admitted.

Let df' := proj1_sig2T _ _ _ Rolle_lemma3.

Let Hdf' : [0] [<] df' := proj2a_sig2T _ _ _ Rolle_lemma3.

Let Hf' :
  forall x y : IR,
  I x ->
  I y ->
  forall Hx Hy,
  AbsIR (x[-]y) [<=] df' -> AbsIR (F' x Hx[-]F' y Hy) [<=] e [/]TwoNZ :=
  proj2b_sig2T _ _ _ Rolle_lemma3.

Let d := Min df df'.

Let Hd : [0] [<] d.
Proof.
Admitted.

Let incF : included (Compact Hab) (Dom F).
Proof.
Admitted.

Let n := compact_nat a b d Hd.

Let fcp (i : nat) (Hi : i <= n) :=
  F (compact_part a b Hab' d Hd i Hi)
    (incF _ (compact_part_hyp a b Hab Hab' d Hd i Hi)).

Let Rolle_lemma1 :
  Sumx (fun (i : nat) (H : i < n) => fcp (S i) H[-]fcp i (Nat.lt_le_incl i n H)) [=]
  [0].
Proof.
Admitted.

Let incF' : included (Compact Hab) (Dom F').
Proof.
Admitted.

Let fcp' (i : nat) (Hi : i <= n) :=
  F' (compact_part a b Hab' d Hd i Hi)
    (incF' _ (compact_part_hyp a b Hab Hab' d Hd i Hi)).

Notation cp := (compact_part a b Hab' d Hd).

Let Rolle_lemma4 :
  {i : nat |
  {H : i < n |
  [0] [<]
  (fcp' _ (Nat.lt_le_incl _ _ H) [+]e) [*] (cp (S i) H[-]cp i (Nat.lt_le_incl _ _ H))}}.
Proof.
Admitted.

Let Rolle_lemma5 : {i : nat | {H : i <= n | [--]e [<] fcp' _ H}}.
Proof.
Admitted.

Let Rolle_lemma6 :
  {i : nat |
  {H : i < n |
  (fcp' _ (Nat.lt_le_incl _ _ H) [-]e) [*] (cp (S i) H[-]cp i (Nat.lt_le_incl _ _ H)) [<]
  [0]}}.
Proof.
Admitted.

Let Rolle_lemma7 : {i : nat | {H : i <= n | fcp' _ H [<] e}}.
Proof.
Admitted.

Let j := ProjT1 Rolle_lemma5.

Let Hj := ProjT1 (ProjT2 Rolle_lemma5).

Let Hj' : [--]e [<] fcp' _ Hj.
Proof.
Admitted.

Let k := ProjT1 Rolle_lemma7.

Let Hk := ProjT1 (ProjT2 Rolle_lemma7).

Let Hk' : fcp' _ Hk [<] e.
Proof.
Admitted.

Let Rolle_lemma8 :
  forall (i : nat) (H : i <= n),
  AbsIR (fcp' _ H) [<] e or e [/]TwoNZ [<] AbsIR (fcp' _ H).
Proof.
Admitted.

Let Rolle_lemma9 :
  {m : nat | {Hm : m <= n | AbsIR (fcp' _ Hm) [<] e}}
  or (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)).
Proof.
Admitted.

Let Rolle_lemma10 :
  {m : nat | {Hm : m <= n | AbsIR (fcp' _ Hm) [<] e}} ->
  {x : IR | I x | forall Hx, AbsIR (F' x Hx) [<=] e}.
Proof.
Admitted.

Let Rolle_lemma11 :
  (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)) ->
  (forall H : 0 <= n, fcp' _ H [<] [--] (e [/]TwoNZ)) ->
  forall (i : nat) (H : i <= n), fcp' _ H [<] [0].
Proof.
Admitted.

Let Rolle_lemma12 :
  (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)) ->
  (forall H : 0 <= n, e [/]TwoNZ [<] fcp' _ H) ->
  forall (i : nat) (H : i <= n), [0] [<] fcp' _ H.
Proof.
Admitted.

Let Rolle_lemma13 :
  (forall (i : nat) (H : i <= n), fcp' _ H [<] [0])
  or (forall (i : nat) (H : i <= n), [0] [<] fcp' _ H) ->
  {x : IR | I x | forall Hx, AbsIR (F' x Hx) [<=] e}.
Proof.
Admitted.

Let Rolle_lemma15 :
  (forall (i : nat) (H : i <= n), e [/]TwoNZ [<] AbsIR (fcp' _ H)) ->
  fcp' _ (Nat.le_0_l n) [<] [--] (e [/]TwoNZ) or e [/]TwoNZ [<] fcp' _ (Nat.le_0_l n).
Proof.
Admitted.
(* end hide *)

Theorem Rolle : {x : IR | I x | forall Hx, AbsIR (F' x Hx) [<=] e}.
Proof.
Admitted.

End Rolle.

Section Law_of_the_Mean.

(**
The following is a simple corollary:
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
Let I := Compact Hab.
(* end hide *)

Variables F F' : PartIR.

Hypothesis HF : Derivative_I Hab' F F'.

(* begin show *)
Hypothesis HA : Dom F a.
Hypothesis HB : Dom F b.
(* end show *)

Lemma Law_of_the_Mean_I : forall e, [0] [<] e ->
 {x : IR | I x | forall Hx, AbsIR (F b HB[-]F a HA[-]F' x Hx[*] (b[-]a)) [<=] e}.
Proof.
Admitted.

End Law_of_the_Mean.

Section Corollaries.

(**
We can also state these theorems without expliciting the derivative of [F].
*)

Variables a b : IR.
Hypothesis Hab' : a [<] b.

(* begin hide *)
Let Hab := less_leEq _ _ _ Hab'.
(* end hide *)
Variable F : PartIR.

(* begin show *)
Hypothesis HF : Diffble_I Hab' F.
(* end show *)

Theorem Rolle' : (forall Ha Hb, F a Ha [=] F b Hb) -> forall e, [0] [<] e ->
 {x : IR | Compact Hab x | forall Hx, AbsIR (PartInt (ProjT1 HF) x Hx) [<=] e}.
Proof.
Admitted.

Lemma Law_of_the_Mean'_I : forall HA HB e, [0] [<] e ->
 {x : IR | Compact Hab x | forall Hx,
  AbsIR (F b HB[-]F a HA[-]PartInt (ProjT1 HF) x Hx[*] (b[-]a)) [<=] e}.
Proof.
Admitted.

End Corollaries.

Section Generalizations.

(**
The mean law is more useful if we abstract [a] and [b] from the
context---allowing them in particular to be equal.  In the case where
[F(a) [=] F(b)] we get Rolle's theorem again, so there is no need to
state it also in this form.

%\begin{convention}% Assume [I] is a proper interval, [F,F':PartIR].
%\end{convention}%
*)

Variable I : interval.
Hypothesis pI : proper I.

Variables F F' : PartIR.
(* begin show *)
Hypothesis derF : Derivative I pI F F'.
(* end show *)

(* begin hide *)
Let incF := Derivative_imp_inc _ _ _ _ derF.
Let incF' := Derivative_imp_inc' _ _ _ _ derF.
(* end hide *)

Theorem Law_of_the_Mean : forall a b, I a -> I b -> forall e, [0] [<] e ->
 {x : IR | Compact (Min_leEq_Max a b) x | forall Ha Hb Hx,
  AbsIR (F b Hb[-]F a Ha[-]F' x Hx[*] (b[-]a)) [<=] e}.
Proof.
Admitted.

(**
We further generalize the mean law by writing as an explicit bound.
*)

Theorem Law_of_the_Mean_Abs_ineq : forall a b, I a -> I b -> forall c,
 (forall x,  Compact (Min_leEq_Max a b) x -> forall Hx, AbsIR (F' x Hx) [<=] c) ->
 forall Ha Hb, AbsIR (F b Hb[-]F a Ha) [<=] c[*]AbsIR (b[-]a).
Proof.
Admitted.

Theorem Law_of_the_Mean_ineq : forall a b, I a -> I b -> forall c,
 (forall x,  Compact (Min_leEq_Max a b) x -> forall Hx, AbsIR (F' x Hx) [<=] c) ->
 forall Ha Hb, F b Hb[-]F a Ha [<=] c[*]AbsIR (b[-]a).
Proof.
Admitted.

End Generalizations.
