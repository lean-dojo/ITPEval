(*
MIT License

Copyright (c) 2020 Frédéric Chardard, Institut Camille Jordan /
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

Require Import Reals.
Open Scope R_scope.


Fixpoint bernoullicoeff (n:nat) (k:nat) : R:=
match n with |  O  => match k with | O => INR 1
                                   | _ => INR 0
                      end
             |(S m)=> 
  match k with 
| O    => (sum_f_R0 (fun l => -((bernoullicoeff m l)*(/INR (S l))*(INR n)*/ INR (S (S l)) )) m)
| (S l)=> (bernoullicoeff m l)*/(INR (S l))*(INR n)
  end
end.


Definition bernoulli_polynomial (n:nat) (x:R):=
(sum_f_R0 (fun l => (bernoullicoeff n l) *x^l) n).


Theorem bernoulli_polynomial_derivable_pt_lim:
forall n:nat,forall x:R,
derivable_pt_lim (bernoulli_polynomial (S n)) x ((bernoulli_polynomial n x)*(INR (S n))).
Proof.
Admitted.

Theorem bernoulli_polynomial_derivable_pt_lim_shift:
forall n:nat,forall x:R,
    derivable_pt_lim (fun x=> (bernoulli_polynomial (S n) (x+1))) x ((bernoulli_polynomial n (x+1))*(INR (S n))).
Proof.
Admitted.


Lemma sumzero : forall n:nat, sum_f_R0 (fun _ => 0:R) n=(0:R).
Proof.
Admitted.

Theorem bernoulli_polynomial_val_0_1:
  forall n:nat,n<>1%nat  -> bernoulli_polynomial n 0=bernoulli_polynomial n 1.
Proof.
Admitted.



Lemma primitive_diff : forall f g fp : (R->R), 
(forall x:R, derivable_pt_lim f x (fp x))->
(forall x:R, derivable_pt_lim g x (fp x))->
forall x:R, f x=(plus_fct g (fct_cte ((f 0)-(g 0)))) x.
Proof.
Admitted.

Lemma primitive_eq:forall f g fp : (R->R), 
(forall x:R, derivable_pt_lim f x (fp x))->
(forall x:R, derivable_pt_lim g x (fp x))->
f 0=g 0->
forall x:R, f x=g x.
Proof.
Admitted.

Lemma kthpowers : forall n:nat, forall x:R,
x^n*(INR (S n))=(bernoulli_polynomial (S n) (x+1))-(bernoulli_polynomial (S n) x).
Proof.
Admitted.

Lemma sum_kthpowers : forall r:nat, forall n:nat, 
(0<r)%nat->
sum_f_R0 (fun k => ((INR k)^r)%R) n
=((bernoulli_polynomial (S r) (INR n+1))-(bernoulli_polynomial (S r) 0))/(INR r+1).
Proof.
Admitted.
