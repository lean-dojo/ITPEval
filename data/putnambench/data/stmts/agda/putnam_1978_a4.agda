-- Statement-only formalization of PutnamBench corpus artifact putnam_1978_a4:
-- a bypass binary operation satisfying (ab)(cd) = ad has the stated
-- idempotence and translation consequences, and admits a finite example
-- satisfying conditions (A), (B), and (C). This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1978A4 where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not :
  {level : Level} ->
  Set level ->
  Set level
Not proposition =
  proposition -> Bottom

_!=_ :
  {level : Level} ->
  {A : Set level} ->
  A ->
  A ->
  Set level
x != y =
  Not (x == y)

record _and_
  {left-level right-level : Level}
  (A : Set left-level)
  (B : Set right-level) :
  Set (left-level ⊔ right-level) where

  constructor both
  field
    first  : A
    second : B

record ExistsPair
  {level property-level : Level}
  (A : Set level)
  (P : A -> A -> Set property-level) :
  Set (level ⊔ property-level) where

  constructor pair-witness
  field
    left     : A
    right    : A
    property : P left right

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Finite
  {level : Level}
  (A : Set level) :
  Set level where

  field
    cardinality : Nat
    toFin        : A -> Fin cardinality
    fromFin      : Fin cardinality -> A
    from-to      : (x : A) -> fromFin (toFin x) == x
    to-from      : (i : Fin cardinality) -> toFin (fromFin i) == i

Bypass :
  {level : Level} ->
  {S : Set level} ->
  (S -> S -> S) ->
  Set level
Bypass multiply =
  (a b c d : _) ->
  multiply (multiply a b) (multiply c d) == multiply a d

record ProductConsequences
  {level : Level}
  {S : Set level}
  (multiply : S -> S -> S)
  (a c : S) :
  Set level where

  field
    product-idempotent :
      multiply c c == c
    same-right-translations :
      (d : S) ->
      multiply a d == multiply c d

UniversalConclusion : Set1
UniversalConclusion =
  (S : Set) ->
  (multiply : S -> S -> S) ->
  Bypass multiply ->
  (a b c : S) ->
  multiply a b == c ->
  ProductConsequences multiply a c

record FiniteBypassExample : Set1 where
  field
    Carrier : Set
    multiply : Carrier -> Carrier -> Carrier
    finite-carrier : Finite Carrier
    bypass :
      Bypass multiply
    condition-A :
      (a : Carrier) ->
      multiply a a == a
    condition-B :
      ExistsPair Carrier
        (\ a b ->
          multiply a b == a
          and
          a != b)
    condition-C :
      ExistsPair Carrier
        (\ a b ->
          multiply a b != a)

putnam-1978-a4 : Set1
putnam-1978-a4 =
  UniversalConclusion
  and
  FiniteBypassExample
