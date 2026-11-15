(*
MIT License

Copyright (c) 2017 Jean-Marie Madiot, INRIA

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

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.

Fixpoint appears x l :=
  match l with
  | [] => false
  | y :: l => if Nat.eqb x y then true else appears x l
  end.

Fixpoint collision l :=
  match l with
  | [] => false
  | x :: l => if appears x l then true else collision l
  end.

Fixpoint enumerate n :=
  match n with
  | 0 => []
  | S n => n :: enumerate n
  end.

Lemma length_enumerate n : length (enumerate n) = n.
Proof.
Admitted.

Lemma filter_app {A} f (l1 l2 : list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
Admitted.

Fixpoint cartesian_product {A B} (xs : list A) (ys : list B) : list (A * B) :=
  match xs with
  | [] => []
  | x :: xs => map (pair x) ys ++ cartesian_product xs ys
  end.

Fixpoint picks {A} n (l : list A) : list (list A) :=
  match n with
  | O => [[]]
  | S n => map (fun x => fst x :: snd x) (cartesian_product l (picks n l))
  end.

Lemma length_cartesian_product {A B} (xs : list A) (ys : list B) :
  length (cartesian_product xs ys) = length xs * length ys.
Proof.
Admitted.

Lemma Zlength_picks {A} n (l : list A) :
  Zlength (picks n l) = Z.
Proof.
Admitted.

Fixpoint partial_fact k n (* = n! / (n-k)! *) :=
  (match k with
   | O => 1
   | S k => n * partial_fact k (n - 1)
   end)%Z.

Definition no {A} (f : A -> bool) x := negb (f x).

Lemma cartesian_product_filters {A B} (f : A -> bool) (g : B -> bool) xs ys :
  cartesian_product (filter f xs) (filter g ys) =
  filter (fun p => andb (f (fst p)) (g (snd p))) (cartesian_product xs ys).
Proof.
Admitted.

Lemma picks_remove k a l :
  picks k (filter (no (Nat.
Proof.
Admitted.

Lemma appears_filter x l f :
  appears x l = false -> appears x (filter f l) = false.
Proof.
Admitted.

Lemma collision_filter l f :
  collision l = false -> collision (filter f l) = false.
Proof.
Admitted.

Lemma collision_count l :
  collision l = false -> Forall (fun x1 : nat => count_occ Nat.
Proof.
Admitted.

Lemma length_no_collision_picks k l :
  collision l = false ->
  Zlength (filter (no collision) (picks k l)) =
  partial_fact k (Zlength l).
Proof.
Admitted.

Lemma length_filter {A} (f : A -> bool) l :
  length (filter f l) + length (filter (no f) l) = length l.
Proof.
Admitted.

Lemma Zlength_filter {A} (f : A -> bool) l :
  (Zlength (filter f l) = Zlength l - Zlength (filter (no f) l))%Z.
Proof.
Admitted.

Lemma enumerate_no_collisions n : collision (enumerate n) = false.
Proof.
Admitted.

Theorem birthday_paradox :
  let l := picks 23 (enumerate 365) in
  2 * length (filter collision l) > length l.
Proof.
Admitted.

Theorem birthday_paradox_min :
  let l := picks 22 (enumerate 365) in
  2 * length (filter collision l) < length l.
Proof.
Admitted.
