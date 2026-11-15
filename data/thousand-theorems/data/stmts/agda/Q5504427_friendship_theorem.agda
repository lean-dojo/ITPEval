-- Statement-only formalization of thousand-theorems corpus artifact Q5504427,
-- "Friendship theorem": every nonempty finite simple graph in which each pair
-- of distinct vertices has exactly one common neighbor has a vertex adjacent
-- to every other vertex. This file contains no proof.

{-# OPTIONS --safe #-}

module Q5504427_friendship_theorem where

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _and_

data Bottom : Set where

Not :
  {p : Level} ->
  Set p ->
  Set p
Not proposition =
  proposition -> Bottom

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor both
  field
    first  : A
    second : B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a lmax p) where

  constructor witness
  field
    value    : A
    property : P value

record ExistsUnique
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a lmax p) where

  constructor unique-witness
  field
    unique-value    : A
    unique-property : P unique-value
    uniqueness      : (other : A) -> P other -> other == unique-value

record Nonempty
  {a : Level}
  (A : Set a) :
  Set a where

  constructor inhabited
  field
    element : A

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

FinitePresentation :
  {a : Level} ->
  Set a ->
  Set a
FinitePresentation A =
  Σ Nat (\ cardinality -> Bijection A (Fin cardinality))

record SimpleGraph
  {a : Level}
  (V : Set a) :
  Set (lsuc a) where

  field
    adjacent  : V -> V -> Set
    loopless  : (v : V) -> Not (adjacent v v)
    symmetric : (v w : V) -> adjacent v w -> adjacent w v

open SimpleGraph

Friendship :
  {a : Level} ->
  {V : Set a} ->
  SimpleGraph V ->
  Set a
Friendship {V = V} graph =
  (v w : V) ->
  Not (v == w) ->
  ExistsUnique V
    (\ common ->
      adjacent graph v common
      and
      adjacent graph w common)

ExistsPolitician :
  {a : Level} ->
  {V : Set a} ->
  SimpleGraph V ->
  Set a
ExistsPolitician {V = V} graph =
  Exists V
    (\ politician ->
      (other : V) ->
      Not (politician == other) ->
      adjacent graph politician other)

friendship-theorem :
  {a : Level} ->
  Set (lsuc a)
friendship-theorem {a} =
  (V : Set a) ->
  FinitePresentation V ->
  Nonempty V ->
  (graph : SimpleGraph V) ->
  Friendship graph ->
  ExistsPolitician graph
