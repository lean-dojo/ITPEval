-- Statement-only formalization of Logipedia corpus artifact bigops.sub_lt
-- (catalog title "bigops.sub_lt"): natural-number bound inclusion induces the
-- identity sub_hk relation on Boolean-selected indices. This file contains no proof.

{-# OPTIONS --safe #-}

module sub_lt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

infix 4 _≤_ _<_
infixr 3 _∧_

data _≤_ (n : Nat) : Nat -> Set where
  le-refl : n ≤ n
  le-step : {m : Nat} -> n ≤ m -> n ≤ suc m

_<_ : Nat -> Nat -> Set
n < m = suc n ≤ m

record _∧_ (A B : Set) : Set where
  field
    first  : A
    second : B

sub-hk :
  (h k : Nat -> Nat) ->
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  Set
sub-hk h k n1 n2 p1 p2 f1 f2 =
  (i : Nat) ->
  i < n1 ->
  p1 i ≡ true ->
  ((h i < n2) ∧ (p2 (h i) ≡ true)) ∧
  (k (h i) ≡ i)

sub-lt : Set
sub-lt =
  (e : Nat -> Nat) ->
  (p : Nat -> Bool) ->
  (n m : Nat) ->
  n ≤ m ->
  sub-hk
    (λ x -> x)
    (λ x -> x)
    n
    m
    p
    p
    e
    e
