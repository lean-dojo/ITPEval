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
Require Import String.
Require Import List.
Require Import Psatz.
Require Import Factorial.

(* Recurrence part of the inductive proof:  *)

Lemma recurrence a b Afirst Bfirst all Afirst_ahead Bfirst_ahead ahead :
  0 < b -> b < a ->
  (a + b) * Afirst = a * all ->
  (a + b) * Bfirst = b * all ->
  Afirst + Bfirst = all ->
  (a - 1 + b) * Afirst_ahead = (a - b - 1) * Afirst ->
  (a - 1 + b) * Bfirst_ahead = (a - (b - 1)) * Bfirst ->
  Afirst_ahead + Bfirst_ahead = ahead ->
  (a + b) * ahead = (a - b) * all.
Proof.
Admitted.

Import ListNotations.

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

Fixpoint pickbools n :=
  match n with
  | O => [[]]
  | S n => map (cons true) (pickbools n) ++ map (cons false) (pickbools n)
  end.

(** non empty suffixes *)
Fixpoint proper_suffixes {A} (l : list A) : list (list A) :=
  match l with
  | [] => []
  | x :: l => (x :: l) :: proper_suffixes l
  end.

(** For our notion of "throughout" we choose that lists represent the
    last vote first, and hence we use suffixes *)
Definition throughout {A} f (l : list A) := forallb f (proper_suffixes l).

Definition countb b l := count_occ Bool.bool_dec l b.

Notation length := length.

Lemma countb_false l : countb false l = length l - countb true l.
Proof.
Admitted.

Definition winb votes := countb false votes <? countb true votes.

Definition sumtrue p l := countb true l =? p.

Lemma filter_app {A} f (l1 l2 : list A) :
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof.
Admitted.

Lemma map_filter {A B} f (g : A -> B) l :
  filter f (map g l) = map g (filter (fun b => f (g b)) l).
Proof.
Admitted.

Lemma filter_filter {A} (f g : A -> bool) l :
  filter f (filter g l) = filter (fun b => andb (g b) (f b)) l.
Proof.
Admitted.

Lemma filter_ext {A} f g l : (forall x : A, f x = g x) -> filter f l = filter g l.
Proof.
Admitted.

Lemma filter_sub {A} f g l : (forall x : A, f x = true -> g x = true) -> filter f l = filter g (filter f l).
Proof.
Admitted.

Fixpoint binomial (n k : nat) : nat :=
  match n with
  | 0 =>
    match k with
    | 0 => 1
    | S _ => 0
    end
  | S n' =>
    match k with
    | 0 => 1
    | S k' => (binomial n' k') + (binomial n' k)
    end
  end.

Lemma binomial_lt n p : n < p -> binomial n p = 0.
Proof.
Admitted.

Lemma binomial_0_r n : binomial n 0 = 1.
Proof.
Admitted.

Lemma binomial_1_r n : binomial n 1 = n.
Proof.
Admitted.

Lemma binomial_diag n : binomial n n = 1.
Proof.
Admitted.

Lemma binomial_factorial n k : k <= n -> fact k * fact (n - k) * binomial n k = fact n.
Proof.
Admitted.

Lemma binomial_complement n k : k <= n -> binomial n k = binomial n (n - k).
Proof.
Admitted.

Lemma binomial_S n k :
  k <= n ->
  S n * binomial n k = S k * binomial (S n) (S k).
Proof.
Admitted.

Lemma count_sumtrue_cons_true p l :
  filter (sumtrue (S p)) (map (cons true) l) =
  map (cons true) (filter (sumtrue p) l).
Proof.
Admitted.

Lemma count_0_wins_cons_true l :
  filter (sumtrue 0) (map (cons true) l) = [].
Proof.
Admitted.

Lemma count_sumtrue_cons_false p l :
  filter (sumtrue p) (map (cons false) l) =
  map (cons false) (filter (sumtrue p) l).
Proof.
Admitted.

Lemma count_sumtrue p n :
  length (filter (sumtrue p) (pickbools n)) = binomial n p.
Proof.
Admitted.

Lemma first_vote_split p q :
  filter (sumtrue (1 + p)) (pickbools (1 + p + q)) =
  map (cons true) (filter (sumtrue p) (pickbools (p + q))) ++
  map (cons false) (filter (sumtrue (1 + p)) (pickbools (p + q))).
Proof.
Admitted.

Lemma pickbools_length n : pickbools n = filter (fun l => length l =? n) (pickbools n).
Proof.
Admitted.

Lemma counting_wins p q :
  q < p ->
  filter winb (filter (sumtrue p) (pickbools (p + q))) =
  filter (sumtrue p) (pickbools (p + q)).
Proof.
Admitted.

Lemma pickbools_wins_minus p q :
  q <= p ->
  (p - q) * length (filter (sumtrue p) (pickbools (p + q))) =
  (p - q) * length (filter winb (filter (sumtrue p) (pickbools (p + q)))).
Proof.
Admitted.
  
Lemma bertrand_ballot_bool_eq p q :
  p <> 0 ->
  p = q ->
  let l := filter (fun votes => countb true votes =? p) (pickbools (p + q)) in
  (p + q) * length (filter (throughout winb) l) =
  (p - q) * length (filter winb l).
Proof.
Admitted.

Theorem bertrand_ballot_bool p q :
  q <= p ->
  let l := filter (sumtrue p) (pickbools (p + q)) in
  (p + q) * length (filter (throughout winb) l) =
  (p - q) * length (filter winb l).
Proof.
Admitted.

Definition count_votes := count_occ string_dec.

Definition wins A B votes := count_votes votes B <? count_votes votes A.

Open Scope string_scope.

(** we enumerate all lists of votes with:
     - p + q votes for (A or B)
     - p votes for A   *)

Theorem bertrand_ballot p q :
  let l := filter (fun votes => count_votes votes "A" =? p)%nat (picks (p + q) ["A"; "B"]) in
  p >= q ->
  (p + q) * List.length (filter (throughout (wins "A" "B")) l) =
  (p - q) * List.length (filter (wins "A" "B") l).
Proof.
Admitted.
