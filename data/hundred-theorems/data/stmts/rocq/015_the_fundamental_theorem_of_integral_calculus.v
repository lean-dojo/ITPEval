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

(** printing [-S-] %\ensuremath{\int}% #&int;# *)

Require Export CoRN.ftc.MoreIntegrals.
Require Export CoRN.ftc.CalculusTheorems.

Opaque Min.

Section Indefinite_Integral.

(**
* The Fundamental Theorem of Calculus

Finally we can prove the fundamental theorem of calculus and its most
important corollaries, which are the main tools to formalize most of
real analysis.

** Indefinite Integrals

We define the indefinite integral of a function in a proper interval.
%\begin{convention}% Let [I : interval], [F : PartIR] be continuous in
[I] and [a] be a point in [I].
%\end{convention}%
*)

Variable I : interval.
Variable F : PartIR.

Hypothesis contF : Continuous I F.

Variable a : IR.
Hypothesis Ha : I a.

Lemma prim_lemma :
  forall x : IR, I x ->
    Continuous_I (Min_leEq_Max a x) F.
Proof.
Admitted.

Lemma Fprim_strext :
  forall x y Hx Hy,
    Integral (prim_lemma x Hx) [#]
      Integral (prim_lemma y Hy) ->
    x [#] y.
Proof.
Admitted.

Definition Fprim : PartIR.
Proof.
Admitted.

End Indefinite_Integral.

Arguments Fprim [I F].

Notation "[-S-] F" := (Fprim F) (at level 20).

Section FTC.

(**
** The FTC

We can now prove our main theorem.  We begin by remarking that the
primitive function is always continuous.

%\begin{convention}% Assume that [J : interval], [F : PartIR] is
continuous in [J] and [x0] is a point in [J].  Denote by [G] the
indefinite integral of [F] from [x0].
%\end{convention}%
*)

Variable J : interval.
Variable F : PartIR.

Hypothesis contF : Continuous J F.

Variable x0 : IR.
Hypothesis Hx0 : J x0.

(* begin hide *)
Let G := ( [-S-]contF) x0 Hx0.
(* end hide *)

Lemma Continuous_prim : Continuous J G.
Proof.
Admitted.

(**
The derivative of [G] is simply [F].
*)

Hypothesis pJ : proper J.

Theorem FTC1 : Derivative J pJ G F.
Proof.
Admitted.

(**
Any other function [G0] with derivative [F] must differ from [G] by a constant.
*)

Variable G0 : PartIR.
Hypothesis derG0 : Derivative J pJ G0 F.

Theorem FTC2 : {c : IR | Feq J (G{-}G0) [-C-]c}.
Proof.
Admitted.

(**
The following is another statement of the Fundamental Theorem of Calculus, also known as Barrow's rule.
*)

End FTC.

Theorem Barrow :
  forall J F (contF : Continuous J F)
    (pJ : proper J) G0
    (derG0 : Derivative J pJ G0 F)
    a b (H : Continuous_I (Min_leEq_Max a b) F) Ha Hb,
    let Ha' := Derivative_imp_inc _ _ _ _ derG0 a Ha in
    let Hb' := Derivative_imp_inc _ _ _ _ derG0 b Hb in
    Integral H [=] G0 b Hb'[-]G0 a Ha'.
Proof.
Admitted.

#[global]
Hint Resolve Continuous_prim: continuous.
#[global]
Hint Resolve FTC1: derivate.

Section Limit_of_Integral_Seq.

(**
** Corollaries

With these tools in our hand, we can prove several useful results.

%\begin{convention}% From this point onwards:
 - [J : interval];
 - [f : nat->PartIR] is a sequence of continuous functions (in [J]);
 - [F : PartIR] is continuous in [J].

%\end{convention}%

In the first place, if a sequence of continuous functions converges
then the sequence of their primitives also converges, and the limit
commutes with the indefinite integral.
*)

Variable J : interval.

Variable f : nat -> PartIR.
Variable F : PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contF : Continuous J F.

Section Compact.

(**
We need to prove this result first for compact intervals.

%\begin{convention}% Assume that [a, b, x0 : IR] with [(f n)] and [F]
continuous in [[a,b]], $x0\in[a,b]$#x0&isin;[a,b]#; denote by
[(g n)] and [G] the indefinite integrals respectively of [(f n)] and
[F] with origin [x0].
%\end{convention}%
*)

Variables a b : IR.
Hypothesis Hab : a [<=] b.
Hypothesis contIf : forall n : nat, Continuous_I Hab (f n).
Hypothesis contIF : Continuous_I Hab F.
(* begin show *)
Hypothesis convF : conv_fun_seq' a b Hab f F contIf contIF.
(* end show *)

Variable x0 : IR.
Hypothesis Hx0 : J x0.
Hypothesis Hx0' : Compact Hab x0.

(* begin hide *)
Let g (n : nat) := ( [-S-]contf n) x0 Hx0.
Let G := ( [-S-]contF) x0 Hx0.
(* end hide *)

(* begin show *)
Hypothesis contg : forall n : nat, Continuous_I Hab (g n).
Hypothesis contG : Continuous_I Hab G.
(* end show *)

Lemma fun_lim_seq_integral : conv_fun_seq' a b Hab g G contg contG.
Proof.
Admitted.

End Compact.

(**
And now we can generalize it step by step.
*)

Lemma limit_of_integral : conv_fun_seq'_IR J f F contf contF -> forall x y Hxy,
 included (Compact Hxy) J -> forall Hf HF,
 Cauchy_Lim_prop2 (fun n => integral x y Hxy (f n) (Hf n)) (integral x y Hxy F HF).
Proof.
Admitted.

Lemma limit_of_Integral : conv_fun_seq'_IR J f F contf contF -> forall x y,
 included (Compact (Min_leEq_Max x y)) J -> forall Hxy Hf HF,
 Cauchy_Lim_prop2 (fun n => Integral (a:=x) (b:=y) (Hab:=Hxy) (F:=f n) (Hf n))
   (Integral (Hab:=Hxy) (F:=F) HF).
Proof.
Admitted.

Section General.

(**
Finally, with [x0, g, G] as before,
*)

(* begin show *)
Hypothesis convF : conv_fun_seq'_IR J f F contf contF.
(* end show *)

Variable x0 : IR.
Hypothesis Hx0 : J x0.

(* begin hide *)
Let g (n : nat) := ( [-S-]contf n) x0 Hx0.
Let G := ( [-S-]contF) x0 Hx0.
(* end hide *)

Hypothesis contg : forall n : nat, Continuous J (g n).
Hypothesis contG : Continuous J G.

Lemma fun_lim_seq_integral_IR : conv_fun_seq'_IR J g G contg contG.
Proof.
Admitted.

End General.

End Limit_of_Integral_Seq.

Section Limit_of_Derivative_Seq.

(**
Similar results hold for the sequence of derivatives of a converging sequence; this time the proof is easier, as we can do it directly for any kind of interval.

%\begin{convention}% Let [g] be the sequence of derivatives of [f] and [G] be the derivative of [F].
%\end{convention}%
*)

Variable J : interval.
Hypothesis pJ : proper J.

Variables f g : nat -> PartIR.
Variables F G : PartIR.

Hypothesis contf : forall n : nat, Continuous J (f n).
Hypothesis contF : Continuous J F.
Hypothesis convF : conv_fun_seq'_IR J f F contf contF.

Hypothesis contg : forall n : nat, Continuous J (g n).
Hypothesis contG : Continuous J G.
Hypothesis convG : conv_fun_seq'_IR J g G contg contG.

Hypothesis derf : forall n : nat, Derivative J pJ (f n) (g n).

Lemma fun_lim_seq_derivative : Derivative J pJ F G.
Proof.
Admitted.

End Limit_of_Derivative_Seq.

Section Derivative_Series.

(**
As a very important case of this result, we get a rule for deriving series.
*)

Variable J : interval.
Hypothesis pJ : proper J.
Variables f g : nat -> PartIR.

(* begin show *)
Hypothesis convF : fun_series_convergent_IR J f.
Hypothesis convG : fun_series_convergent_IR J g.
(* end show *)
Hypothesis derF : forall n : nat, Derivative J pJ (f n) (g n).

Lemma Derivative_FSeries : Derivative J pJ (FSeries_Sum convF) (FSeries_Sum convG).
Proof.
Admitted.

End Derivative_Series.
