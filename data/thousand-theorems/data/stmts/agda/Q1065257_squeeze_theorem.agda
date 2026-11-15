-- Statement-only formalization of thousand-theorems corpus artifact Q1065257,
-- "Squeeze theorem": for functions into a preordered space with its order
-- topology, eventual lower and upper bounds converging to the same point force
-- the bounded function to converge there. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1065257_squeeze_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor top

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

Subset :
  {a p : Level} →
  Set a →
  Set (a ⊔ lsuc p)
Subset {p = p} X =
  X → Set p

Whole :
  {a p : Level} →
  {X : Set a} →
  Subset {p = p} X
Whole _ =
  Top

Intersection :
  {a p : Level} →
  {X : Set a} →
  Subset {p = p} X →
  Subset {p = p} X →
  Subset {p = p} X
Intersection U V x =
  U x × V x

SubsetOf :
  {a p : Level} →
  {X : Set a} →
  Subset {p = p} X →
  Subset {p = p} X →
  Set (a ⊔ p)
SubsetOf {X = X} U V =
  (x : X) →
  U x →
  V x

record Preorder
  {a p : Level}
  (X : Set a) :
  Set (a ⊔ lsuc p) where

  field
    le :
      X →
      X →
      Set p

    le-reflexive :
      (x : X) →
      le x x

    le-transitive :
      (x y z : X) →
      le x y →
      le y z →
      le x z

open Preorder

StrictLess :
  {a p : Level} →
  {X : Set a} →
  Preorder {p = p} X →
  X →
  X →
  Set p
StrictLess order x y =
  le order x y × Not (le order y x)

record Filter
  {a p : Level}
  (X : Set a) :
  Set (a ⊔ lsuc p) where

  field
    eventually :
      Subset {p = p} X →
      Set p

    eventually-whole :
      eventually Whole

    eventually-upward :
      (U V : Subset {p = p} X) →
      eventually U →
      SubsetOf U V →
      eventually V

    eventually-intersection :
      (U V : Subset {p = p} X) →
      eventually U →
      eventually V →
      eventually (Intersection U V)

open Filter

data OrderRay
  {a : Level}
  (X : Set a) :
  Set a where

  above : X → OrderRay X
  below : X → OrderRay X

RayContains :
  {a p : Level} →
  {X : Set a} →
  Preorder {p = p} X →
  OrderRay X →
  X →
  Set p
RayContains order (above lower) x =
  StrictLess order lower x
RayContains order (below upper) x =
  StrictLess order x upper

All :
  {a b : Level} →
  {A : Set a} →
  (P : A → Set b) →
  List A →
  Set b
All P [] =
  Top
All P (x ∷ xs) =
  P x × All P xs

BasicContains :
  {a p : Level} →
  {X : Set a} →
  Preorder {p = p} X →
  List (OrderRay X) →
  X →
  Set p
BasicContains order rays x =
  All (λ ray → RayContains order ray x) rays

OrderNeighborhood :
  {a p : Level} →
  {X : Set a} →
  Preorder {p = p} X →
  X →
  Subset {p = p} X →
  Set (a ⊔ p)
OrderNeighborhood {X = X} order x U =
  Σ (List (OrderRay X))
    (λ rays →
      BasicContains order rays x
      ×
      SubsetOf (BasicContains order rays) U)

Tendsto :
  {a b p : Level} →
  {X : Set a} →
  {Y : Set b} →
  Preorder {p = p} X →
  Filter {p = p} Y →
  (Y → X) →
  X →
  Set (a ⊔ lsuc p)
Tendsto {p = p} {X = X} order source-filter function limit =
  (U : Subset {p = p} X) →
  OrderNeighborhood order limit U →
  eventually source-filter (λ y → U (function y))

squeeze-theorem :
  {a b : Level} →
  Set (lsuc (a ⊔ b))
squeeze-theorem {a} {b} =
  (X : Set a) →
  (Y : Set b) →
  (order : Preorder {p = a ⊔ b} X) →
  (source-filter : Filter {p = a ⊔ b} Y) →
  (f g h : Y → X) →
  (limit : X) →
  Tendsto order source-filter g limit →
  Tendsto order source-filter h limit →
  eventually source-filter (λ y → le order (g y) (f y)) →
  eventually source-filter (λ y → le order (f y) (h y)) →
  Tendsto order source-filter f limit
