-- Statement-only formalization of thousand-theorems corpus artifact Q765987,
-- "Heine–Cantor theorem": every continuous function from a compact uniform
-- space to a uniform space is uniformly continuous. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module Q765987_heine_cantor_theorem where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

record Top {a : Level} : Set a where
  constructor top

record Both
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A ->
  Set a where

  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)

  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

Predicate :
  {a q : Level} ->
  Set a ->
  Set (lsuc (a ⊔ q))
Predicate {a} {q} X =
  X -> Set (a ⊔ q)

Relation :
  {a q : Level} ->
  Set a ->
  Set (lsuc (a ⊔ q))
Relation {a} {q} X =
  X -> X -> Set (a ⊔ q)

PredicateSubset :
  {a q : Level} ->
  {X : Set a} ->
  Predicate {q = q} X ->
  Predicate {q = q} X ->
  Set (a ⊔ q)
PredicateSubset {X = X} U V =
  (x : X) ->
  U x ->
  V x

RelationSubset :
  {a q : Level} ->
  {X : Set a} ->
  Relation {q = q} X ->
  Relation {q = q} X ->
  Set (a ⊔ q)
RelationSubset {X = X} U V =
  (x y : X) ->
  U x y ->
  V x y

WholeRelation :
  {a q : Level} ->
  {X : Set a} ->
  Relation {q = q} X
WholeRelation _ _ =
  Top

IntersectionRelation :
  {a q : Level} ->
  {X : Set a} ->
  Relation {q = q} X ->
  Relation {q = q} X ->
  Relation {q = q} X
IntersectionRelation U V x y =
  Both (U x y) (V x y)

Converse :
  {a q : Level} ->
  {X : Set a} ->
  Relation {q = q} X ->
  Relation {q = q} X
Converse U x y =
  U y x

Compose :
  {a q : Level} ->
  {X : Set a} ->
  Relation {q = q} X ->
  Relation {q = q} X ->
  Relation {q = q} X
Compose {X = X} U V x z =
  Σ X
    (λ y ->
      Both (U x y) (V y z))

record UniformSpace
  {a q : Level}
  (X : Set a) :
  Set (lsuc (a ⊔ q)) where

  field
    entourage :
      Relation {q = q} X ->
      Set (a ⊔ q)

    entourage-whole :
      entourage
        (WholeRelation {a = a} {q = q} {X = X})

    entourage-upward :
      (U V : Relation {q = q} X) ->
      entourage U ->
      RelationSubset {a = a} {q = q} {X = X} U V ->
      entourage V

    entourage-intersection :
      (U V : Relation {q = q} X) ->
      entourage U ->
      entourage V ->
      entourage
        (IntersectionRelation {a = a} {q = q} {X = X} U V)

    entourage-diagonal :
      (U : Relation {q = q} X) ->
      entourage U ->
      (x : X) ->
      U x x

    entourage-converse :
      (U : Relation {q = q} X) ->
      entourage U ->
      entourage
        (Converse {a = a} {q = q} {X = X} U)

    entourage-square-root :
      (U : Relation {q = q} X) ->
      entourage U ->
      Σ (Relation {q = q} X)
        (λ V ->
          Both
            (entourage V)
            (RelationSubset
              {a = a} {q = q} {X = X}
              (Compose {a = a} {q = q} {X = X} V V)
              U))

open UniformSpace

Neighborhood :
  {a q : Level} ->
  {X : Set a} ->
  UniformSpace {q = q} X ->
  X ->
  Predicate {q = q} X ->
  Set (lsuc (a ⊔ q))
Neighborhood {a = a} {q = q} {X = X} uniformity x U =
  Σ (Relation {q = q} X)
    (λ V ->
      Both
        (entourage
          {a = a} {q = q} {X = X}
          uniformity V)
        ((y : X) ->
          V x y ->
          U y))

IsOpen :
  {a q : Level} ->
  {X : Set a} ->
  UniformSpace {q = q} X ->
  Predicate {q = q} X ->
  Set (lsuc (a ⊔ q))
IsOpen {X = X} uniformity U =
  (x : X) ->
  U x ->
  Neighborhood uniformity x U

CoversWhole :
  {a q i : Level} ->
  {X : Set a} ->
  {I : Set i} ->
  (I -> Predicate {q = q} X) ->
  Set (a ⊔ q ⊔ i)
CoversWhole {X = X} {I = I} sets =
  (x : X) ->
  Σ I
    (λ i ->
      sets i x)

FiniteSubcover :
  {a q i : Level} ->
  {X : Set a} ->
  {I : Set i} ->
  (I -> Predicate {q = q} X) ->
  Set (a ⊔ q ⊔ i)
FiniteSubcover {X = X} {I = I} sets =
  Σ (List I)
    (λ selected ->
      (x : X) ->
      Σ I
        (λ i ->
          Both
            (Member i selected)
            (sets i x)))

CompactSpace :
  {a q : Level} ->
  {X : Set a} ->
  UniformSpace {q = q} X ->
  Setω
CompactSpace {a = a} {q = q} {X = X} uniformity =
  (i : Level) ->
  (I : Set i) ->
  (sets : I -> Predicate {a = a} {q = q} X) ->
  ((index : I) ->
    IsOpen {a = a} {q = q} {X = X}
      uniformity (sets index)) ->
  CoversWhole {a = a} {q = q} {i = i} {X = X} {I = I} sets ->
  FiniteSubcover {a = a} {q = q} {i = i} {X = X} {I = I} sets

Continuous :
  {a b : Level} ->
  {X : Set a} ->
  {Y : Set b} ->
  UniformSpace {q = b} X ->
  UniformSpace {q = a} Y ->
  (X -> Y) ->
  Set (lsuc (a ⊔ b))
Continuous {a = a} {b = b} {X = X} {Y = Y}
  source target function =
  (x : X) ->
  (U : Predicate {a = b} {q = a} Y) ->
  Neighborhood {a = b} {q = a} {X = Y}
    target (function x) U ->
  Neighborhood {a = a} {q = b} {X = X}
    source x
    (λ y ->
      U (function y))

UniformContinuous :
  {a b : Level} ->
  {X : Set a} ->
  {Y : Set b} ->
  UniformSpace {q = b} X ->
  UniformSpace {q = a} Y ->
  (X -> Y) ->
  Set (lsuc (a ⊔ b))
UniformContinuous {a = a} {b = b} {X = X} {Y = Y}
  source target function =
  (V : Relation {a = b} {q = a} Y) ->
  entourage {a = b} {q = a} {X = Y}
    target V ->
  entourage {a = a} {q = b} {X = X}
    source
    (λ x y ->
      V (function x) (function y))

heine-cantor-theorem : Setω
heine-cantor-theorem =
  (a b : Level) ->
  (X : Set a) ->
  (Y : Set b) ->
  (source : UniformSpace {q = b} X) ->
  (target : UniformSpace {q = a} Y) ->
  CompactSpace source ->
  (function : X -> Y) ->
  Continuous source target function ->
  UniformContinuous source target function
