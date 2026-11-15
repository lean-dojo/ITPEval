-- Statement-only formalization of thousand-theorems corpus artifact Q474881
-- (thousand-theorems__agda__Q474881), "Cantor's theorem": no function from a
-- type onto its powerset is surjective, with subsets identified by pointwise
-- logical equivalence. This file contains no proof.

{-# OPTIONS --safe #-}

module Q474881_cantor_s_theorem where

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

Powerset :
  {a : Level} ->
  (p : Level) ->
  Set a ->
  Set (a lmax lsuc p)
Powerset p X =
  X -> Set p

record LogicalEquivalence
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a lmax b) where

  constructor logically-equivalent
  field
    forward : left -> right
    backward : right -> left

SameSubset :
  {a p : Level} ->
  {X : Set a} ->
  Powerset p X ->
  Powerset p X ->
  Set (a lmax p)
SameSubset {X = X} left right =
  (x : X) ->
  LogicalEquivalence
    (left x)
    (right x)

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a lmax p) where

  constructor witness
  field
    value : A
    property : P value

Surjective :
  {a p : Level} ->
  {X : Set a} ->
  (X -> Powerset p X) ->
  Set (a lmax lsuc p)
Surjective {p = p} {X = X} f =
  (target : Powerset p X) ->
  Exists X (\ source -> SameSubset (f source) target)

cantor-surjective :
  {a p : Level} ->
  Set (lsuc (a lmax p))
cantor-surjective {a} {p} =
  (X : Set a) ->
  (f : X -> Powerset p X) ->
  Not (Surjective f)
