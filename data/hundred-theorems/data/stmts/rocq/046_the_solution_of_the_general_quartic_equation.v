(*
MIT License

Copyright (c) 2017-2020 Frédéric Chardard, Institut Camille Jordan /
Université Jean Monnet de Saint-Etienne

Permission is hereby granted, free of charge, to any person obtaining a copy 
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*)


(*
This file contains:
_A construction of a nth-root of complex numbers.
_A construction of a cubic root on C such that if the argument is real, 
then the result is also real.
_A proof that Cardan-Tartaglia formula solves the general cubic equation 
in the field of complex numbers.
__A proof that Ferrari method solves the general quartic equation in the 
field of complex numbers.


This file was checked by Coq without error with following configuration:
base-bigarray          base
base-threads           base
base-unix              base
cairo2                 0.6.1       Binding to Cairo, a 2D Vector Graphics Library
conf-cairo             1           Virtual package relying on a Cairo system installation
conf-findutils         1           Virtual package relying on findutils
conf-g++               1.0         Virtual package relying on the g++ compiler (for C++)
conf-gnome-icon-theme3 0           Virtual package relying on gnome-icon-theme
conf-gtk3              18          Virtual package relying on GTK+ 3
conf-gtksourceview3    0+2         Virtual package relying on a GtkSourceView-3 system installation
conf-m4                1           Virtual package relying on m4
conf-pkg-config        1.3         Virtual package relying on pkg-config installation
coq                    8.12.0      Formal proof management system
coq-coquelicot         3.1.0       A Coq formalization of real analysis compatible with the standard library
coq-mathcomp-ssreflect 1.11.0      Small Scale Reflection
coqide                 8.12.0      IDE of the Coq formal proof management system
dune                   2.7.0       Fast, portable, and opinionated build system
dune-configurator      2.7.0       Helper library for gathering system configuration
lablgtk3               3.1.1       OCaml interface to GTK+3
lablgtk3-sourceview3   3.1.1       OCaml interface to GTK+ gtksourceview library
num                    1.3         The legacy Num library for arbitrary-precision integer and rational arithmetic
ocaml                  4.08.1      The OCaml compiler (virtual package)
ocaml-config           1           OCaml Switch Configuration
ocaml-system           4.08.1      The OCaml compiler (system version, from outside of opam)
ocamlfind              1.8.1       A library manager for OCaml

on Linux empmeticj012 5.4.0-42-generic #46-Ubuntu SMP Fri Jul 10 00:24:02 UTC 2020 x86_64 x86_64 x86_64 GNU/Linux
(Ubuntu 20.04.1 LTS)
with OPAM 2.0.5.
*)

Require Import Reals Coq.Reals.Rtrigo_def Coquelicot.Coquelicot Coquelicot.ElemFct Lra.



Open Scope R_scope.

Ltac Rsimpl:=
repeat (
try rewrite Ropp_involutive;
try rewrite Ropp_0;
try rewrite Rplus_opp_l;
try rewrite Rplus_opp_r;
try rewrite Rplus_0_l;
try rewrite Rplus_0_r;
try rewrite Rmult_1_l;
try rewrite Rmult_1_r;
try rewrite Rmult_0_l;
try rewrite Rmult_0_r
).


Ltac Csimpl:=
  repeat (
      try rewrite Copp_0;
      try rewrite Cplus_opp_r;
      try rewrite Cplus_0_l;
      try rewrite Cplus_0_r;
      try rewrite Cmult_0_r;
      try rewrite Cmult_1_r;
      try rewrite Cmult_0_l;
      try rewrite Cmult_1_l).


Lemma contraposition_neg : forall P Q:Prop, ( P -> Q ) -> ( (~Q) -> (~P)).
Proof.
Admitted.


Definition Rneg_or_not : forall z:C,
 {0<Re z} + {Im z<>0} + {Im z=0 /\ Re z<=0}.
Proof.
intros.
destruct z as (u,v).
unfold Im, Re, fst, snd.
unfold Rle.
destruct (total_order_T u 0) as [uneg|uspos];
  try destruct uneg as [usneg|u0];
  destruct (Reqdec v) as [veq0|vneq0];
  auto.
Qed.


Definition Csqrt:=fun (z:C) =>
let (u,v):=z in
let a:=(sqrt(((Cmod z)+u)/2))%R in
let b:=(if (Rneg_or_not z) 
   then v/2/a
   else  sqrt(-u))%R in
(a,b)%C : C.


Lemma Csqrt_Cpow2 : forall z: C, (Csqrt z)*(Csqrt z)=z.
Proof.
Admitted.



Definition cargument (z: C) : R := 
if (Rneg_or_not z) then (INR 2)*atan((Im (Csqrt z))/(Re (Csqrt z))) 
else PI.

Lemma trigoform: forall z : C,
                   z=(cos(cargument z),sin(cargument z))*(Cmod z,0).
Proof.
Admitted.
 
Lemma factorisationdeg3 : forall z1 z2 z3:C, forall z:C, 
(z-z1)*(z-z2)*(z-z3)=Cpow z 3+(-(z1+z2+z3))*Cpow z 2+(z1*z2+z2*z3+z3*z1)*z+(-(z1*z2*z3)).
Proof.
Admitted.





Theorem Cpowexp : forall n:nat, forall x:R, ((exp(x))^n=exp((INR n)*x)) % R.
Proof.
Admitted.

Theorem comCpow: forall n : nat, forall z:C, forall u:C, (Cpow (z*u)%C n)=((Cpow z n)*(Cpow u n))%C.
Proof.
Admitted.


Lemma RCpow : forall n:nat,forall x:R, Cpow (x,0)%C n = ((x^n)%R,0)%C.
Proof.
Admitted.



Definition nroot (n:nat) (z:C) : C:= 
if Ceq_dec z 0 then  0 
else let argn:=((cargument z)/(INR n))%R in
  (cos(argn),sin(argn))*(exp((ln (Cmod z))/(INR n)),0).


Theorem nroot_Cpown : forall n:nat,forall z:C,n<>O-> Cpow (nroot n z) n=z.
Proof.
Admitted.

Lemma nrootpositive : forall x:R, forall n:nat, 0<=x -> Im( nroot n x ) =0%R.
Proof.
Admitted.

Definition cubicroot (z:C) := if(Rcase_abs (Re z)) then -nroot 3 (-z) else nroot 3 z.

Lemma cubicroot3 : forall z:C, Cpow (cubicroot z) 3=z.
Proof.
Admitted.

Lemma cubicrootreal : forall (x:R), 0%R=Im (cubicroot x).
Proof.
Admitted.

Definition CJ := ((-/2)%R,(sqrt (3/4))%R)%C.

Lemma CJ2: CJ*CJ=-CJ-1.
Proof.
Admitted.

Lemma CJ3 : CJ*CJ*CJ=1%C.
Proof.
Admitted.

Lemma Cval2 : RtoC 2=RtoC 1+RtoC 1.
Proof.
Admitted.
Lemma Cval3 : RtoC 3=RtoC 1+RtoC 1+RtoC 1.
Proof.
Admitted.
Lemma Cval4: (RtoC 4=(RtoC 1+RtoC 1)*(RtoC 1+RtoC 1)).
Proof.
Admitted.
Lemma Cval6 : RtoC 6=(RtoC 1+RtoC 1+RtoC 1)*(RtoC 1+RtoC 1).
Proof.
Admitted.
Lemma Cval8 : RtoC 8=(RtoC 1+RtoC 1)*(RtoC 1+RtoC 1)*(RtoC 1+RtoC 1).
Proof.
Admitted.


Lemma shiftdeg3 : forall u:C, forall a b c:C, forall z:C, 
Cpow (z+u) 3+a*Cpow (z+u) 2+b*(z+u)+c
=Cpow z 3+(a+3*u)*Cpow z 2+(b+2*u*a+3*Cpow u 2)*z+(c+b*u+a*Cpow u 2+Cpow u 3).
Proof.
Admitted.

Lemma permprod: forall e f g:C,  g*f*e=e*g*f.
Proof.
Admitted.

Ltac nneq0:=unfold RtoC;
injection;
intro;
lra.

Ltac developall:=
  unfold Cpow;
  repeat (try Csimpl;
          try rewrite Cmult_plus_distr_r;
          try rewrite Cmult_plus_distr_l);
  repeat (
          repeat rewrite (permprod CJ);
          repeat rewrite Cmult_assoc).




Definition Cardan_Tartaglia_formula:=fun (a1:C) (a2:C) (a3:C) (n:nat) =>
let s:=-a1/3 in 
let p:=a2+2*s*a1+3*Cpow s 2 in
let q:=a3+a2*s+a1*Cpow s 2+Cpow s 3 in
let Delta:=(Cpow (q/2) 2)+(Cpow (p/3) 3) in
let alpha : C :=if(Ceq_dec p 0) then (RtoC 0) else (cubicroot (-(q/2)+Csqrt Delta)) in
let beta:=if(Ceq_dec p 0) then -cubicroot q else -(p/3)/alpha in
s+(alpha*Cpow CJ n+beta*Cpow CJ (n+n)).


Theorem Cardan_Tartaglia : forall a1 a2 a3 :C,
let u1:=(Cardan_Tartaglia_formula a1 a2 a3 0) in
let u2:=(Cardan_Tartaglia_formula a1 a2 a3 1) in
let u3:=(Cardan_Tartaglia_formula a1 a2 a3 2) in
forall u:C, (u-u1)*(u-u2)*(u-u3)=Cpow u 3+a1*Cpow u 2+a2*u+a3.
Proof.
Admitted.

Lemma shiftdeg4 : forall u:C, forall a b c d:C, forall z:C, 
Cpow (z+u) 4+a*Cpow (z+u) 3+b*Cpow (z+u) 2+c*(z+u)+d
=Cpow z 4+(a+4*u)*Cpow z 3+(b+3*u*a+6*Cpow u 2)*Cpow z 2
 +(c+2*b*u+3*a*Cpow u 2+4*Cpow u 3)*z+(d+c*u+b*Cpow u 2+a*Cpow u 3+Cpow u 4).
Proof.
Admitted.

Definition binom_solution:= fun (b:C) (c:C) (n:nat) =>
-b/2+(Csqrt (Cpow (b/2) 2-c))*Cpow (-1) n.

Lemma Binom_solution_proof : forall (b:C) (c:C), forall z:C,
Cpow z 2+b*z+c=(z-binom_solution b c 0)*(z-binom_solution b c 1).
Proof.
Admitted.

Theorem Ferrari_formula: forall (a:C) (b:C) (c:C) (d:C), 
let s:=-a/4 in 
let p:= b+3*s*a+6*Cpow s 2 in
let q:= c+2*b*s+3*a*Cpow s 2+4*Cpow s 3 in
let r:= d+c*s+b*Cpow s 2+a*Cpow s 3+Cpow s 4 in
let lambda:=Cardan_Tartaglia_formula (-p/2) (-r) (r*p/2-/8*Cpow q 2) 0 in
let A:=Csqrt(2*lambda-p) in
let cond:=(Ceq_dec (2*lambda) p) in
let B:=if cond then (RtoC 0) else (-q/(2*A)) in
let z1:=if cond then Csqrt (binom_solution p r 0) 
                else binom_solution A (B+lambda) 0 in
let z2:=if cond then -Csqrt (binom_solution p r 0) 
                else binom_solution A (B+lambda) 1 in
let z3:=if cond then Csqrt (binom_solution p r 1) 
                else binom_solution (-A) (-B+lambda) 0 in
let z4:=if cond then -Csqrt (binom_solution p r 1) 
                else binom_solution (-A) (-B+lambda) 1 in
let u1:=z1+s in
let u2:=z2+s in
let u3:=z3+s in
let u4:=z4+s in
forall u:C, (u-u1)*(u-u2)*(u-u3)*(u-u4)=Cpow u 4+a*Cpow u 3+b*Cpow u 2+c*u+d.
Proof.
Admitted.
