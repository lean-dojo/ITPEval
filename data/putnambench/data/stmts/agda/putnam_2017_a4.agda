-- Statement-only formalization of PutnamBench corpus artifact putnam_2017_a4
-- (putnambench__agda__putnam_2017_a4): partitioning a class with quiz scores
-- 0 through 10 into two equal-size groups, each retaining average 7.4.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero = zero
finToNat (fsuc i) = suc (finToNat i)

sumFin : {n : Nat} -> (Fin n -> Nat) -> Nat
sumFin {zero} term = zero
sumFin {suc n} term =
  term fzero + sumFin (\ i -> term (fsuc i))

boolToNat : Bool -> Nat
boolToNat false = zero
boolToNat true = suc zero

notBool : Bool -> Bool
notBool false = true
notBool true = false

selectedCount :
  {n : Nat} ->
  (Fin n -> Bool) ->
  Nat
selectedCount selected =
  sumFin (\ i -> boolToNat (selected i))

selectedScoreSum :
  {n : Nat} ->
  (Fin n -> Fin 11) ->
  (Fin n -> Bool) ->
  Nat
selectedScoreSum score selected =
  sumFin
    (\ i ->
      boolToNat (selected i) * finToNat (score i))

totalScoreSum :
  {n : Nat} ->
  (Fin n -> Fin 11) ->
  Nat
totalScoreSum score =
  sumFin (\ i -> finToNat (score i))

AverageIsSevenPointFour : Nat -> Nat -> Set
AverageIsSevenPointFour scoreSum studentCount =
  5 * scoreSum == 37 * studentCount

Surjective :
  {m n : Nat} ->
  (Fin m -> Fin n) ->
  Set
Surjective score =
  (k : _) ->
  Exists _ (\ i -> score i == k)

putnam-2017-a4 : Set
putnam-2017-a4 =
  (N : Nat) ->
  (score : Fin (2 * N) -> Fin 11) ->
  Surjective score ->
  AverageIsSevenPointFour
    (totalScoreSum score)
    (2 * N) ->
  Exists (Fin (2 * N) -> Bool)
    (\ selected ->
      selectedCount selected == N
      and
      (AverageIsSevenPointFour
        (selectedScoreSum score selected)
        N
      and
      AverageIsSevenPointFour
        (selectedScoreSum score (\ i -> notBool (selected i)))
        N))
