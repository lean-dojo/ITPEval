-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_b2:
-- every element of a finite group is a product of two elements of any subset
-- containing more than half of the group. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<N_
infixr 3 _and_

record Top : Set where
  constructor truth

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

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record HasCardinality
  {a p : Level}
  {A : Set a}
  (P : A -> Set p)
  (cardinality : Nat) :
  Set (a ⊔ p) where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (index : Fin cardinality) ->
      P (enumerate index)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ index -> x == enumerate index)
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      enumerate left-index == enumerate right-index ->
      left-index == right-index

record FiniteCarrier
  {a : Level}
  (A : Set a) :
  Set a where

  field
    cardinality :
      Nat
    has-cardinality :
      HasCardinality {A = A} (\ _ -> Top) cardinality

record FiniteSubset
  {a p : Level}
  {A : Set a}
  (P : A -> Set p) :
  Set (a ⊔ p) where

  field
    cardinality :
      Nat
    has-cardinality :
      HasCardinality P cardinality

record Group
  {a : Level}
  (G : Set a) :
  Set a where

  field
    identity :
      G
    multiply :
      G ->
      G ->
      G
    inverse :
      G ->
      G
    multiply-associative :
      (x y z : G) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    identity-left :
      (x : G) ->
      multiply identity x == x
    identity-right :
      (x : G) ->
      multiply x identity == x
    inverse-left :
      (x : G) ->
      multiply (inverse x) x == identity
    inverse-right :
      (x : G) ->
      multiply x (inverse x) == identity

open FiniteCarrier
open FiniteSubset
open Group

two : Nat
two =
  suc (suc zero)

putnam-1968-b2 :
  {a p : Level} ->
  Set (lsuc (a ⊔ p))
putnam-1968-b2 {a} {p} =
  (G : Set a) ->
  (group : Group G) ->
  (A : G -> Set p) ->
  (finite-group : FiniteCarrier G) ->
  (finite-A : FiniteSubset A) ->
  cardinality finite-group <N two * cardinality finite-A ->
  (g : G) ->
  Exists G
    (\ x ->
      A x
      and
      Exists G
        (\ y ->
          A y
          and
          g == multiply group x y))
