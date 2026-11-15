-- Statement-only formalization of Thousand Theorems artifact Q1188392,
-- "Zeckendorf's theorem": every natural number has a unique finite decreasing list of
-- nonconsecutive Fibonacci indices at least two whose Fibonacci values sum to that number.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q1188392_zeckendorf_s_theorem where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _<=_

data _<=_ : Nat -> Nat -> Set where
  zero<= : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

one : Nat
one = suc zero

two : Nat
two = suc one

fib : Nat -> Nat
fib zero = zero
fib (suc zero) = one
fib (suc (suc n)) = fib (suc n) + fib n

sumFib : List Nat -> Nat
sumFib [] = zero
sumFib (index ∷ indices) = fib index + sumFib indices

data IsZeckendorfRep : List Nat -> Set where
  zeckendorf-nil :
    IsZeckendorfRep []
  zeckendorf-single :
    {index : Nat} ->
    two <= index ->
    IsZeckendorfRep (index ∷ [])
  zeckendorf-cons :
    {first second : Nat} ->
    {rest : List Nat} ->
    second + two <= first ->
    IsZeckendorfRep (second ∷ rest) ->
    IsZeckendorfRep (first ∷ second ∷ rest)

record UniqueZeckendorfRepresentation (n : Nat) : Set where
  field
    indices :
      List Nat
    valid :
      IsZeckendorfRep indices
    sums-to :
      sumFib indices == n
    unique :
      (other : List Nat) ->
      IsZeckendorfRep other ->
      sumFib other == n ->
      other == indices

zeckendorfEquiv : Set
zeckendorfEquiv =
  (n : Nat) ->
  UniqueZeckendorfRepresentation n
