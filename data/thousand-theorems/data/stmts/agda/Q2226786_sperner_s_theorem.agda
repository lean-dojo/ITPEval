-- Statement-only formalization of thousand-theorems corpus artifact Q2226786,
-- "Sperner's theorem": an inclusion antichain of subsets of an n-element
-- finite set has at most choose n (floor (n / 2)) members. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module Q2226786_sperner_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_ _is-subset-of_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not proposition =
  proposition -> Bottom

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n k + choose n (suc k)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A -> B
    from    : B -> A
    from-to : (x : A) -> from (to x) == x
    to-from : (y : B) -> to (from y) == y

Subset :
  {a : Level} ->
  Set a ->
  Set a
Subset A =
  A -> Bool

data IsTrue : Bool -> Set where
  true-witness : IsTrue true

_is-subset-of_ :
  {a : Level} ->
  {A : Set a} ->
  Subset A ->
  Subset A ->
  Set a
_is-subset-of_ {A = A} left right =
  (x : A) ->
  IsTrue (left x) ->
  IsTrue (right x)

SameSubset :
  {a : Level} ->
  {A : Set a} ->
  Subset A ->
  Subset A ->
  Set a
SameSubset {A = A} left right =
  (x : A) ->
  left x == right x

record FiniteFamily
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size : Nat
    enumerate : Fin size -> Subset A
    no-duplicates :
      (left-index right-index : Fin size) ->
      SameSubset (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

open FiniteFamily

Antichain :
  {a : Level} ->
  {A : Set a} ->
  FiniteFamily A ->
  Set a
Antichain family =
  (left-index right-index : Fin (size family)) ->
  Not (left-index == right-index) ->
  Not
    (enumerate family left-index
      is-subset-of
     enumerate family right-index)

sperner-s-theorem :
  {a : Level} ->
  Set (lsuc a)
sperner-s-theorem {a} =
  (A : Set a) ->
  (n : Nat) ->
  Bijection A (Fin n) ->
  (family : FiniteFamily A) ->
  Antichain family ->
  size family <= choose n (half n)
