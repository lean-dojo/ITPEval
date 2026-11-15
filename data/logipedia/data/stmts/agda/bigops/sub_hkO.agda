-- Statement-only formalization of Logipedia corpus artifact bigops.sub_hkO
-- (catalog title "bigops.sub_hkO"): a zero source bound implies the sub_hk
-- relation on Boolean-selected natural-number indices. This file contains no proof.

{-# OPTIONS --safe #-}

module sub_hkO where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<succ : {n : Nat} -> zero < suc n
  succ<succ : {m n : Nat} -> m < n -> suc m < suc n

record And (A B : Set) : Set where
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
  p1 i == true ->
  And
    (And (h i < n2) (p2 (h i) == true))
    (k (h i) == i)

sub-hkO : Set
sub-hkO =
  (h k : Nat -> Nat) ->
  (n1 n2 : Nat) ->
  (p1 p2 : Nat -> Bool) ->
  (f1 f2 : Nat -> Nat) ->
  n1 == zero ->
  sub-hk h k n1 n2 p1 p2 f1 f2
