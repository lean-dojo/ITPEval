-- Statement-only formalization of thousand-theorems corpus artifact Q918099,
-- "Ramsey's theorem": every finite coloring of the r-element subsets of an
-- infinite subset of the natural numbers has an infinite monochromatic subset.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q918099_ramsey_s_theorem where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_ _<_
infixr 3 _and_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

data Member
  {A : Set}
  (x : A) :
  List A ->
  Set where

  at-head :
    {xs : List A} ->
    Member x (x ∷ xs)

  in-tail :
    {y : A} ->
    {xs : List A} ->
    Member x xs ->
    Member x (y ∷ xs)

data NoDuplicates
  {A : Set} :
  List A ->
  Set where

  no-duplicates-empty :
    NoDuplicates []

  no-duplicates-cons :
    {x : A} ->
    {xs : List A} ->
    Not (Member x xs) ->
    NoDuplicates xs ->
    NoDuplicates (x ∷ xs)

record FiniteSubset
  (A : Set) :
  Set where

  field
    elements      : List A
    no-duplicates : NoDuplicates elements

open FiniteSubset

length :
  {A : Set} ->
  List A ->
  Nat
length [] =
  zero
length (_ ∷ xs) =
  suc (length xs)

-- A nonempty code `finite-from first gaps` denotes the strictly increasing
-- sequence beginning at `first`, with each next entry one plus the preceding
-- entry and the corresponding gap. Thus every finite subset of Nat has a
-- unique code, so arbitrary colorings are genuinely colorings of finite sets.
data FiniteNatSet : Set where
  finite-empty :
    FiniteNatSet

  finite-from :
    Nat ->
    List Nat ->
    FiniteNatSet

cardinality :
  FiniteNatSet ->
  Nat
cardinality finite-empty =
  zero
cardinality (finite-from first gaps) =
  suc (length gaps)

AllFrom :
  (Nat -> Set) ->
  Nat ->
  List Nat ->
  Set
AllFrom member current [] =
  member current
AllFrom member current (gap ∷ gaps) =
  member current
  and
  AllFrom member (suc (current + gap)) gaps

AllElements :
  (Nat -> Set) ->
  FiniteNatSet ->
  Set
AllElements member finite-empty =
  Bottom -> Bottom
AllElements member (finite-from first gaps) =
  AllFrom member first gaps

SubsetOf :
  (Nat -> Set) ->
  (Nat -> Set) ->
  Set
SubsetOf child parent =
  (n : Nat) ->
  child n ->
  parent n

Infinite :
  (Nat -> Set) ->
  Set
Infinite member =
  (bound : Nat) ->
  Exists Nat
    (\ n ->
      member n
      and
      bound < n)

IsEdge :
  Nat ->
  (Nat -> Set) ->
  FiniteNatSet ->
  Set
IsEdge r vertices edge =
  cardinality edge == r
  and
  AllElements vertices edge

ramsey-r : Set₁
ramsey-r =
  (A : Set) ->
  (colors : FiniteSubset A) ->
  (r : Nat) ->
  (M1 : Nat -> Set) ->
  Infinite M1 ->
  (coloring : FiniteNatSet -> A) ->
  ((edge : FiniteNatSet) ->
    IsEdge r M1 edge ->
    Member (coloring edge) (elements colors)) ->
  Exists (Nat -> Set)
    (\ M2 ->
      SubsetOf M2 M1
      and
      Infinite M2
      and
      Exists A
        (\ color ->
          Member color (elements colors)
          and
          ((edge : FiniteNatSet) ->
            IsEdge r M2 edge ->
            coloring edge == color)))
