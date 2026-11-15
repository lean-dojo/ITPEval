(*
Copyright © 2009 Valentin Blot

Permission is hereby granted, free of charge, to any person obtaining a copy of
this proof and associated documentation files (the "Proof"), to deal in
the Proof without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Proof, and to permit persons to whom the Proof is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Proof.

THE PROOF IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE PROOF OR THE USE OR OTHER DEALINGS IN THE PROOF.
*)
Require Import CRing_Homomorphisms.
Require Import CPoly_NthCoeff.
Require Import MoreFunctions.
Require Import Rolle.

Require Import Zlcm Q_can RX_deg QX_ZX QX_root_loc QX_extract_roots.

Section CPoly_bounded.

Variable I : interval.
Hypothesis I_fin : finite I.

Fixpoint AbsPoly (P : cpoly_cring IR) : cpoly_cring IR :=
  match P with
    | cpoly_zero _ => cpoly_zero IR
    | cpoly_linear _ c P => cpoly_linear IR (AbsIR c) (AbsPoly P)
  end.

Lemma AbsPoly_zero : AbsPoly [0] = [0].
Proof.
Admitted.
Lemma AbsPoly_linear : forall c P, AbsPoly (c[+X*]P) = AbsIR c[+X*]AbsPoly P.
Proof.
Admitted.

Lemma Abs_poly_nth_coeff : forall P i, nth_coeff i (AbsPoly P) [=] AbsIR (nth_coeff i P).
Proof.
Admitted.

Definition CPoly_bound (P : cpoly_cring IR)  : IR :=
            (AbsPoly P) ! (Max (AbsIR (left_end I I_fin)) (AbsIR (right_end I I_fin))).

Lemma AbsIR_leEq : forall a b, a [<=] b -> [--]a [<=] b -> AbsIR a [<=] b.
Proof.
Admitted.

Lemma abs_max : forall a b x, a [<=] x -> x [<=] b -> AbsIR x [<=] Max (AbsIR a) (AbsIR b).
Proof.
Admitted.

Lemma Abs_min_max : forall x, I x ->
        AbsIR x [<=] Max (AbsIR (left_end I I_fin)) (AbsIR (right_end I I_fin)).
Proof.
Admitted.

Lemma CPoly_bound_spec : forall x P, I x -> AbsIR (P ! x) [<=] CPoly_bound P.
Proof.
Admitted.

End CPoly_bounded.

Section poly_law_of_mean.

Variable I : interval.
Hypothesis I_fin : finite I.
Hypothesis I_proper : proper I.
Variable P : cpoly_cring IR.

Let C := CPoly_bound I I_fin (_D_ P).
Let Hderiv := Derivative_poly I I_proper P.

Lemma poly_law_of_mean : forall a b, I a -> I b ->
     AbsIR (P ! b [-] P ! a) [<=] C [*] (AbsIR (b [-] a)).
Proof.
Admitted.

End poly_law_of_mean.

Section liouville_lemmas.

Variable a : IR.
Definition Ia : interval := clcr (a[-]Two) (a[+]Two).
Lemma Ia_fin : finite Ia.
Proof.
Admitted.
Lemma Ia_proper : proper Ia.
Proof.
Admitted.
Lemma a_in_Ia : Ia a.
Proof.
Admitted.

Lemma Liouville_lemma1 : forall x : IR, AbsIR (x[-]a) [<=] Two -> Ia x.
Proof.
Admitted.

Variable P : cpoly_cring IR.
Let C := CPoly_bound Ia Ia_fin (_D_ P).

Lemma Liouville_lemma2 : forall x : IR, AbsIR (x[-]a) [<=] Two ->
    AbsIR (P ! x [-] P ! a) [<=] C [*] AbsIR (x [-] a).
Proof.
Admitted.

Lemma Liouville_lemma3 : forall x : IR, [1] [<] x or x [<] Two.
Proof.
Admitted.

End liouville_lemmas.

Section liouville_lemmas2.

Let ZX_deg := RX_deg Z_as_CRing Z_dec.
Variable P : cpoly_cring Z_as_CRing.

Lemma Liouville_lemma4 : forall p : Z_as_CRing,
            p [#] [0] -> [1] [<=] AbsIR (inj_Q_rh p).
Proof.
Admitted.

Lemma Liouville_lemma5 : forall (p : Z_as_CRing) (q : positive), (zx2qx P) ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](ZX_deg P) [*] AbsIR (inj_Q_rh ((zx2qx P) ! (p#q)%Q)).
Proof.
Admitted.

End liouville_lemmas2.

Section liouville_lemmas3.

Let ZX_deg := RX_deg Z_as_CRing Z_dec.
Let QX_deg := RX_deg Q_as_CRing Q_dec.
Variable P : cpoly_cring Q_as_CRing.

Lemma Liouville_lemma6 : forall (p : Z_as_CRing) (q : positive), P ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] AbsIR (inj_Q_rh ((Zlcm_den_poly P:Q_as_CRing)[*]P ! (p#q)%Q)).
Proof.
Admitted.

Lemma Liouville_lemma7 : forall (p : Z_as_CRing) (q : positive), P ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] AbsIR (inj_Q_rh (Zlcm_den_poly P:Q_as_CRing)) [*] AbsIR (inj_Q_rh (P ! (p#q)%Q)).
Proof.
Admitted.

Variable a : IR.
Let C := AbsIR (inj_Q_rh (Zlcm_den_poly P:Q_as_CRing)) [*] CPoly_bound (Ia a) (Ia_fin a) (_D_ (inj_QX_rh P)).
Hypothesis Ha : (inj_QX_rh P) ! a [=] [0].

Lemma Liouville_lemma8 : forall (n : nat) (q : positive), [1] [<=] (inj_Q_rh q)[^]n.
Proof.
Admitted.

Lemma Liouville_lemma9 : forall (p : Z_as_CRing) (q : positive),
      P ! (p#q)%Q [#] [0] -> AbsIR ((inj_Q_rh (p#q)%Q) [-] a) [<=] Two ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] C [*] AbsIR ((inj_Q_rh (p#q)%Q) [-] a).
Proof.
Admitted.

Let C' := Max [1] C.

Lemma Liouville_lemma10 : forall (p : Z_as_CRing) (q : positive),
      P ! (p#q)%Q [#] [0] ->
      [1] [<=] (inj_Q_rh q)[^](QX_deg P) [*] C' [*] AbsIR ((inj_Q_rh (p#q)%Q) [-] a).
Proof.
Admitted.

End liouville_lemmas3.

Section liouville_theorem.

Variable a : IR.
Hypothesis a_irrat : forall x : Q, a [~=] inj_Q _ x.
Variable P : cpoly_cring Q_as_CRing.
Hypothesis P_nz : P [#] [0].
Hypothesis a_alg : (inj_QX_rh P) ! a [=] [0].

Let C : IR := Max [1] (AbsIR (inj_Q_rh (Zlcm_den_poly (QX_extract_roots P):Q_as_CRing)) [*] CPoly_bound (Ia a) (Ia_fin a) (_D_ (inj_QX_rh (QX_extract_roots P)))).
Lemma constant_pos : [0] [<] C.
Proof.
Admitted.

Lemma constant_nz : C [#] [0].
Proof.
Admitted.

Definition Liouville_constant : IR := [1] [/] C [//] constant_nz.

Definition Liouville_degree := RX_deg _ Q_dec (QX_extract_roots P).

Theorem Liouville_theorem : forall (x : Q),
       (Liouville_constant[*]inj_Q IR (1#Qden x)%Q[^]Liouville_degree)
                             [<=] AbsIR (inj_Q _ x [-] a).
Proof.
Admitted.

Theorem Liouville_theorem2 :
    {n : nat | {C : IR | [0] [<] C | forall (x : Q),
         (C[*]inj_Q IR (1#Qden x)%Q[^]n) [<=] AbsIR (inj_Q _ x [-] a)}}.
Proof.
Admitted.

End liouville_theorem.
