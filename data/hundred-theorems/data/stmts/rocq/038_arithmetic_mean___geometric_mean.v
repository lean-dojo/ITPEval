(*
MIT License

Copyright (c) 2016 Jean-Marie Madiot, Princeton University

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

Require Import Lia Reals Psatz.

Open Scope R_scope.

Tactic Notation "assert_specialize" hyp(H) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp; [ | specialize (H Htemp); try clear Htemp ]
  end.

Tactic Notation "assert_specialize" hyp(H) "by" tactic(tac) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp by tac; specialize (H Htemp); try clear Htemp
  end.

Ltac exact_eq H :=
  revert H;
  match goal with
    |- ?p -> ?q => cut (p = q); [intros ->; auto | ]
  end.

Lemma base x y : 4 * (x * y) <= (x + y) * (x + y).
Proof.
Admitted.

Lemma base' x y : (x * y) <= (x + y) * (x + y) / 4.
Proof.
Admitted.

Lemma base_strict x y : x <> y -> 4 * (x * y) < (x + y) * (x + y).
Proof.
Admitted.

Lemma mean2 x y :
  0 <= x ->
  0 <= y ->
  sqrt (x * y) <= (x + y) / 2.
Proof.
Admitted.

Lemma mean2_strict x y :
  0 <= x ->
  0 <= y ->
  x <> y ->
  sqrt (x * y) < (x + y) / 2.
Proof.
Admitted.


Lemma mean2_ge x y :
  0 <= x ->
  0 <= y ->
  sqrt (x * y) >= (x + y) / 2 ->
  x = y.
Proof.
Admitted.

Lemma mean2_rev x y :
  0 <= x ->
  0 <= y ->
  sqrt (x * y) = (x + y) / 2 ->
  x = y.
Proof.
Admitted.

Lemma Rdiv_fold x y : x * / y = x / y.
Proof.
Admitted.

Lemma mean_aux x1 y1 x2 y2 :
  0 <= x1 -> 0 <= y1 -> 
  x1 <= x2 -> y1 <= y2 ->
  sqrt (x1 * y1) = (x2 + y2) / 2 ->
  x1 = x2 /\ y1 = y2 /\ x1 = y1.
Proof.
Admitted.

Definition shift {X} n (u : nat -> X) : nat -> X := fun i => u (plus i n).

Fixpoint sum n u := match n with O => 0 | S n => u O + sum n (shift 1 u) end.

Fixpoint prod n u := match n with O => 1 | S n => u O * prod n (shift 1 u) end.

Fixpoint pow2 n := (match n with O => 1 | S n => 2 * pow2 n end)%nat.

Lemma sum_ext n u v : (forall x, u x = v x) -> sum n u = sum n v.
Proof.
Admitted.

Lemma prod_ext n u v : (forall x, u x = v x) -> prod n u = prod n v.
Proof.
Admitted.

Lemma sum_ext_lt n u v : (forall i, lt i n -> u i = v i) -> sum n u = sum n v.
Proof.
Admitted.

Lemma prod_ext_lt n u v : (forall i, lt i n -> u i = v i) -> prod n u = prod n v.
Proof.
Admitted.

Lemma sum_plus n m u : sum (n + m) u = sum n u + sum m (shift n u).
Proof.
Admitted.

Lemma prod_plus n m u : prod (n + m) u = prod n u * prod m (shift n u).
Proof.
Admitted.

Lemma prod_pos n u : (forall i, 0 <= u i) -> 0 <= prod n u.
Proof.
Admitted.

Lemma sum_pos n u : (forall i, 0 <= u i) -> 0 <= sum n u.
Proof.
Admitted.

Lemma sum_pos_lt n u : (forall i, lt i n -> 0 <= u i) -> 0 <= sum n u.
Proof.
Admitted.

Definition sqrtk k := Nat.iter k sqrt.

Lemma sqrtk_pos k a : 0 <= a -> 0 <= sqrtk k a.
Proof.
Admitted.

Lemma sqrtk_mult k a b : 0 <= a -> 0 <= b -> sqrtk k (a * b) = sqrtk k a * sqrtk k b.
Proof.
Admitted.

Lemma pow2_sqrtk k a : 0 <= a -> pow (sqrtk k a) (pow2 k) = a.
Proof.
Admitted.

Lemma sqrtk_pow2 k a : 0 <= a -> sqrtk k (pow a (pow2 k)) = a.
Proof.
Admitted.

Lemma INR_pow2 k : 0 < INR (pow2 k).
Proof.
Admitted.

Lemma mean_power_of_two a :
  (forall i, 0 <= a i) ->
  forall k,
    sqrtk k (prod (pow2 k) a) <=
    sum (pow2 k) a / INR (pow2 k).
Proof.
Admitted.

Lemma mean_power_of_two_eq a :
  (forall i, 0 <= a i) ->
  forall k,
    sqrtk k (prod (pow2 k) a) = sum (pow2 k) a / INR (pow2 k) ->
    forall i j, lt i (pow2 k) -> lt j (pow2 k) -> a i = a j.
Proof.
Admitted.

Theorem geometric_arithmetic_mean (a : nat -> R) (n : nat) :
  n <> O ->
  (forall i, (i < n)%nat -> 0 <= a i) ->
  prod n a <= (sum n a / INR n) ^ n
  /\
  (prod n a = (sum n a / INR n) ^ n -> forall i, (i < n)%nat -> a i = a O).
Proof.
Admitted.
