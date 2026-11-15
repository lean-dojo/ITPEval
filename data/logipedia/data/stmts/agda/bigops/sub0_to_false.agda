-- Statement-only formalization of Logipedia corpus artifact bigops.sub0_to_false
-- (catalog title "bigops.sub0_to_false"): a zero target bound in the sub_hk
-- relation forces the source Boolean predicate to be false below its bound.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module sub0_to_false where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<_
infixr 3 _∧_

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < suc n
  succ<succ : {m n : Nat} -> m < n -> suc m < suc n

record _∧_ (A B : Set) : Set where
  field
    first : A
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
  (h i < n2 ∧ p2 (h i) ≡ true) ∧ k (h i) ≡ i

sub0-to-false : Set
sub0-to-false =
  (h k : Nat -> Nat) ->
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  n1 ≡ zero ->
  sub-hk h k n2 n1 p2 p1 f2 f1 ->
  (i : Nat) ->
  i < n2 ->
  p2 i ≡ false
