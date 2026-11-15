-- Statement-only formalization of thousand-theorems corpus artifact Q976607
-- (thousand-theorems__agda__Q976607), "Erdős–Szekeres theorem": an injective
-- sequence indexed by a finite linear order with more than r * s terms has a
-- finite increasing subsequence of size greater than r or a finite decreasing
-- subsequence of size greater than s. This file contains no proof.

{-# OPTIONS --safe #-}

module Q976607_erd_s_szekeres_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not {a} proposition =
  proposition -> Bottom {a}

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

Injective :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) ->
  function x == function y ->
  x == y

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size      : Nat
    enumerate : Fin size -> A
    complete  :
      (x : A) ->
      Exists (Fin size) (\ index -> enumerate index == x)
    distinct  : Injective enumerate

record LinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    less-than : A -> A -> Set a
    irreflexive :
      (x : A) ->
      Not (less-than x x)
    transitive :
      (x y z : A) ->
      less-than x y ->
      less-than y z ->
      less-than x z
    trichotomy :
      (x y : A) ->
      less-than x y or
      (x == y or less-than y x)

record FiniteSubset
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size      : Nat
    enumerate : Fin size -> A
    distinct  : Injective enumerate

StrictMonoOn :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  LinearOrder A ->
  LinearOrder B ->
  (A -> B) ->
  FiniteSubset A ->
  Set (a ⊔ b)
StrictMonoOn orderA orderB function subset =
  (left-index right-index : Fin (FiniteSubset.size subset)) ->
  LinearOrder.less-than orderA
    (FiniteSubset.enumerate subset left-index)
    (FiniteSubset.enumerate subset right-index) ->
  LinearOrder.less-than orderB
    (function (FiniteSubset.enumerate subset left-index))
    (function (FiniteSubset.enumerate subset right-index))

StrictAntiOn :
  {a b : Level} ->
  {A : Set a} ->
  {B : Set b} ->
  LinearOrder A ->
  LinearOrder B ->
  (A -> B) ->
  FiniteSubset A ->
  Set (a ⊔ b)
StrictAntiOn orderA orderB function subset =
  (left-index right-index : Fin (FiniteSubset.size subset)) ->
  LinearOrder.less-than orderA
    (FiniteSubset.enumerate subset left-index)
    (FiniteSubset.enumerate subset right-index) ->
  LinearOrder.less-than orderB
    (function (FiniteSubset.enumerate subset right-index))
    (function (FiniteSubset.enumerate subset left-index))

erdos-szekeres-theorem :
  {a b : Level} ->
  Set (lsuc (a ⊔ b))
erdos-szekeres-theorem {a} {b} =
  (A : Set a) ->
  (B : Set b) ->
  (finiteA : Finite A) ->
  (orderA : LinearOrder A) ->
  (orderB : LinearOrder B) ->
  (r s : Nat) ->
  (function : A -> B) ->
  r * s <N Finite.size finiteA ->
  Injective function ->
  (Exists (FiniteSubset A)
    (\ subset ->
      (r <N FiniteSubset.size subset)
      and
      StrictMonoOn orderA orderB function subset))
  or
  (Exists (FiniteSubset A)
    (\ subset ->
      (s <N FiniteSubset.size subset)
      and
      StrictAntiOn orderA orderB function subset))
