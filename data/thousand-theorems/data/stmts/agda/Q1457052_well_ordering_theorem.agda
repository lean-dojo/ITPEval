-- Statement-only formalization of Thousand Theorems artifact
-- thousand-theorems__agda__Q1457052, "Well-ordering theorem": every type
-- admits a linear order whose strict relation is well-founded.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1457052_well_ordering_theorem where

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

data Bottom : Set where

Not :
  {p : Level} ->
  Set p ->
  Set p
Not proposition =
  proposition -> Bottom

data Decidable
  {p : Level}
  (proposition : Set p) :
  Set p where

  yes : proposition -> Decidable proposition
  no  : Not proposition -> Decidable proposition

IsProposition :
  {p : Level} ->
  Set p ->
  Set p
IsProposition proposition =
  (left right : proposition) ->
  left == right

record And
  {p q : Level}
  (left : Set p)
  (right : Set q) :
  Set (p lmax q) where

  constructor both
  field
    first  : left
    second : right

data Either
  {p q : Level}
  (left : Set p)
  (right : Set q) :
  Set (p lmax q) where

  left-case  : left -> Either left right
  right-case : right -> Either left right

record LinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    le : A -> A -> Set a
    le-is-proposition :
      (x y : A) ->
      IsProposition (le x y)
    le-decidable :
      (x y : A) ->
      Decidable (le x y)
    le-reflexive :
      (x : A) ->
      le x x
    le-antisymmetric :
      (x y : A) ->
      le x y ->
      le y x ->
      x == y
    le-transitive :
      (x y z : A) ->
      le x y ->
      le y z ->
      le x z
    le-total :
      (x y : A) ->
      Either (le x y) (le y x)

open LinearOrder using (le)

Strict :
  {a : Level} ->
  {A : Set a} ->
  LinearOrder A ->
  A ->
  A ->
  Set a
Strict order x y =
  And (le order x y) (Not (le order y x))

data Accessible
  {a r : Level}
  {A : Set a}
  (relation : A -> A -> Set r)
  (x : A) :
  Set (a lmax r) where

  accessible :
    ((y : A) -> relation y x -> Accessible relation y) ->
    Accessible relation x

WellFounded :
  {a r : Level} ->
  {A : Set a} ->
  (A -> A -> Set r) ->
  Set (a lmax r)
WellFounded {A = A} relation =
  (x : A) -> Accessible relation x

record Exists
  {a p : Level}
  (A : Set a)
  (property : A -> Set p) :
  Set (a lmax p) where

  constructor witness
  field
    value : A
    satisfies : property value

well-ordering-theorem :
  {a : Level} ->
  Set (lsuc a)
well-ordering-theorem {a} =
  (A : Set a) ->
  Exists (LinearOrder A) (\ order -> WellFounded (Strict order))
