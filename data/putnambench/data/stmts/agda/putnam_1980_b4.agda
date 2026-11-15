-- Statement-only formalization of PutnamBench corpus artifact putnam_1980_b4:
-- among 1066 subsets of a finite set, each containing more than half of its
-- elements, there is a ten-element subset meeting every one. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1980B4 where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=N_ _<N_
infixr 3 _and_

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record FiniteSubset
  {a : Level}
  (T : Set a) :
  Set a where

  field
    cardinality : Nat
    element : Fin cardinality -> T
    injective :
      (i j : Fin cardinality) ->
      element i == element j ->
      i == j

open FiniteSubset

Member :
  {a : Level} ->
  {T : Set a} ->
  T ->
  FiniteSubset T ->
  Set a
Member x S =
  Exists (Fin (cardinality S))
    (\ i -> x == element S i)

SubsetOf :
  {a : Level} ->
  {T : Set a} ->
  FiniteSubset T ->
  FiniteSubset T ->
  Set a
SubsetOf {T = T} S U =
  (x : T) ->
  Member x S ->
  Member x U

Meets :
  {a : Level} ->
  {T : Set a} ->
  FiniteSubset T ->
  FiniteSubset T ->
  Set a
Meets {T = T} S U =
  Exists T
    (\ x -> Member x S and Member x U)

putnam-1980-b4 :
  {a : Level} ->
  Set (lsuc a)
putnam-1980-b4 {a} =
  (T : Set a) ->
  (X : FiniteSubset T) ->
  (A : Fin 1066 -> FiniteSubset T) ->
  10 <=N cardinality X ->
  ((i : Fin 1066) ->
    SubsetOf (A i) X
    and
    cardinality X <N 2 * cardinality (A i)) ->
  Exists (FiniteSubset T)
    (\ Y ->
      SubsetOf Y X
      and
      cardinality Y == 10
      and
      ((i : Fin 1066) -> Meets Y (A i)))
