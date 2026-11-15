-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__063,
-- "Cantor's Theorem": for every type, no function from that type onto its
-- universe-polymorphic powerset is surjective up to pointwise logical equivalence.
-- This file contains no proof.

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

record HProp (a : Level) : Set (lsuc a) where
  constructor proposition
  field
    Carrier : Set a
    carrier-is-proposition :
      (left right : Carrier) ->
      left == right

open HProp using (Carrier)

Powerset :
  {a : Level} ->
  (p : Level) ->
  Set a ->
  Set (a lmax lsuc p)
Powerset p X =
  X -> HProp p

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
    (Carrier (left x))
    (Carrier (right x))

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

cantors-theorem :
  {a p : Level} ->
  Set (lsuc (a lmax p))
cantors-theorem {a} {p} =
  (X : Set a) ->
  (f : X -> Powerset p X) ->
  Not (Surjective f)
