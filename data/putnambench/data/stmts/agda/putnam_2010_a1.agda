-- Statement-only formalization of PutnamBench corpus artifact putnam_2010_a1:
-- for every positive n, ceil(n / 2) is the largest number of boxes into which
-- 1 through n can be partitioned with equal box sums. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2010A1 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤N_

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data _≤N_ : Nat -> Nat -> Set where
  zero≤N   : {n : Nat} -> zero ≤N n
  suc≤sucN : {m n : Nat} -> m ≤N n -> suc m ≤N suc n

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

finEqual : {n : Nat} -> Fin n -> Fin n -> Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc _) =
  false
finEqual (fsuc _) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

whenTrue : Bool -> Nat -> Nat
whenTrue true value =
  value
whenTrue false value =
  zero

sumFin : {n : Nat} -> (Fin n -> Nat) -> Nat
sumFin {zero} term =
  zero
sumFin {suc n} term =
  term fzero + sumFin (λ i -> term (fsuc i))

boxSum :
  {n k : Nat} ->
  (Fin n -> Fin k) ->
  Fin k ->
  Nat
boxSum boxes box =
  sumFin
    (λ index ->
      whenTrue
        (finEqual (boxes index) box)
        (suc (finToNat index)))

EqualBoxSums :
  {n k : Nat} ->
  (Fin n -> Fin k) ->
  Set
EqualBoxSums {k = k} boxes =
  (i j : Fin k) ->
  boxSum boxes i ≡ boxSum boxes j

HasEqualPartition : Nat -> Nat -> Set
HasEqualPartition n k =
  Σ (Fin n -> Fin k) EqualBoxSums

ceilingHalf : Nat -> Nat
ceilingHalf zero =
  zero
ceilingHalf (suc zero) =
  suc zero
ceilingHalf (suc (suc n)) =
  suc (ceilingHalf n)

record IsGreatestPartition (n greatest : Nat) : Set where
  field
    attainable :
      HasEqualPartition n greatest
    upper-bound :
      (k : Nat) ->
      HasEqualPartition n k ->
      k ≤N greatest

putnam-2010-a1 : Set
putnam-2010-a1 =
  (n : Nat) ->
  Positive n ->
  IsGreatestPartition n (ceilingHalf n)
