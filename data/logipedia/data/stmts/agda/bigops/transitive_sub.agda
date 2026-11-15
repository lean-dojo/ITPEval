-- Statement-only formalization of Logipedia corpus artifact bigops.transitive_sub
-- (catalog title "bigops.transitive_sub"): the sub_hk relation on selected
-- indices is transitive under composition. Its final two source parameters are
-- retained even though the source definition does not inspect them.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module transitive_sub where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<_
infixr 3 _∧_

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < suc n
  succ<succ : {m n : Nat} -> m < n -> suc m < suc n

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

transitive-sub : Set
transitive-sub =
  (h1 k1 h2 k2 : Nat -> Nat) ->
  (n1 n2 n3 : Nat) ->
  (p1 p2 p3 : Nat -> Bool) ->
  (f1 f2 f3 : Nat -> Nat) ->
  sub-hk h1 k1 n1 n2 p1 p2 f1 f2 ->
  sub-hk h2 k2 n2 n3 p2 p3 f2 f3 ->
  sub-hk
    (λ x -> h2 (h1 x))
    (λ x -> k1 (k2 x))
    n1
    n3
    p1
    p3
    f1
    f3
