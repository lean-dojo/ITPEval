-- Statement-only formalization of thousand-theorems corpus artifact Q536640,
-- "Hall's marriage theorem": a family of finite sets has an injective system
-- of representatives exactly when every finite subfamily has a union at least
-- as large as that subfamily. This file contains no proof.

{-# OPTIONS --safe #-}

module Q536640_hall_s_marriage_theorem where

open import Agda.Primitive using (Level; lsuc) renaming (_⊔_ to _lmax_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc)

infixr 3 _and_
infix 2 _iff_

data Bottom : Set where

data Dec
  {p : Level}
  (P : Set p) :
  Set p where

  yes : P -> Dec P
  no  : (P -> Bottom) -> Dec P

DecidableEquality :
  {a : Level} ->
  Set a ->
  Set a
DecidableEquality A =
  (x y : A) ->
  Dec (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor both
  field
    first  : A
    second : B

record _iff_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a lmax b) where

  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists
  {a p : Level}
  (A : Set a)
  (P : A -> Set p) :
  Set (a lmax p) where

  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a lmax b)
Injective {A = A} function =
  (x y : A) ->
  function x == function y ->
  x == y

record FiniteSubset
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size      : Nat
    enumerate : Fin size -> A
    distinct  : Injective enumerate

open FiniteSubset

Member :
  {a : Level} ->
  {A : Set a} ->
  FiniteSubset A ->
  A ->
  Set a
Member subset item =
  Exists (Fin (size subset))
    (\ index -> item == enumerate subset index)

UnionMember :
  {i a : Level} ->
  {I : Set i} ->
  {A : Set a} ->
  (I -> FiniteSubset A) ->
  FiniteSubset I ->
  A ->
  Set a
UnionMember family indices item =
  Exists (Fin (size indices))
    (\ index ->
      Member
        (family (enumerate indices index))
        item)

HasAtLeast :
  {a p : Level} ->
  {A : Set a} ->
  (A -> Set p) ->
  Nat ->
  Set (a lmax p)
HasAtLeast {A = A} member cardinality =
  Exists (Fin cardinality -> A)
    (\ representatives ->
      Injective representatives
      and
      ((index : Fin cardinality) ->
        member (representatives index)))

HallCondition :
  {i a : Level} ->
  {I : Set i} ->
  {A : Set a} ->
  (I -> FiniteSubset A) ->
  Set (i lmax a)
HallCondition family =
  (indices : FiniteSubset _) ->
  HasAtLeast
    (UnionMember family indices)
    (size indices)

Matching :
  {i a : Level} ->
  {I : Set i} ->
  {A : Set a} ->
  (I -> FiniteSubset A) ->
  Set (i lmax a)
Matching {I = I} {A = A} family =
  Exists (I -> A)
    (\ representative ->
      Injective representative
      and
      ((index : I) ->
        Member (family index) (representative index)))

hall-s-marriage-theorem :
  {i a : Level} ->
  Set (lsuc (i lmax a))
hall-s-marriage-theorem {i} {a} =
  (I : Set i) ->
  (A : Set a) ->
  DecidableEquality A ->
  (family : I -> FiniteSubset A) ->
  HallCondition family
  iff
  Matching family
