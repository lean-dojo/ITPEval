-- Statement-only formalization of PutnamBench corpus artifact putnam_2012_a2
-- (putnambench__agda__putnam_2012_a2): cancellation for a commutative
-- associative operation whose right translations are surjective. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2012A2 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  field
    witness  : A
    property : P witness

putnam-2012-a2 :
  {ℓ : Level} ->
  Set (lsuc ℓ)
putnam-2012-a2 {ℓ} =
  (S : Set ℓ) ->
  (operation : S -> S -> S) ->
  ((x y : S) ->
    operation x y == operation y x) ->
  ((x y z : S) ->
    operation (operation x y) z ==
    operation x (operation y z)) ->
  ((x y : S) ->
    Exists S (\ z -> operation x z == y)) ->
  (a b c : S) ->
  operation a c == operation b c ->
  a == b
