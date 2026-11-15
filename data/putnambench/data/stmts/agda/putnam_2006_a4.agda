-- Statement-only formalization of PutnamBench corpus artifact putnam_2006_a4
-- (putnambench__agda__putnam_2006_a4): the average number of local maxima
-- among all permutations of an n-element set is (n + 1) / 3 for n > 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<N_
infixr 5 _::_

record Exists (A : Set) (P : A -> Set) : Set where
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

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc i) =
  suc (toNat i)

data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

lookup :
  {A : Set} ->
  {n : Nat} ->
  Vec A n ->
  Fin n ->
  A
lookup (x :: xs) fzero =
  x
lookup (x :: xs) (fsuc i) =
  lookup xs i

record HasCardinality
  {A : Set}
  (P : A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumerated-member :
      (i : Fin cardinality) ->
      P (enumerate i)
    enumeration-complete :
      (x : A) ->
      P x ->
      Exists (Fin cardinality)
        (\ i -> x == enumerate i)
    enumeration-injective :
      (i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j

open HasCardinality

lessBool : Nat -> Nat -> Bool
lessBool zero zero =
  false
lessBool zero (suc n) =
  true
lessBool (suc m) zero =
  false
lessBool (suc m) (suc n) =
  lessBool m n

andBool : Bool -> Bool -> Bool
andBool true right =
  right
andBool false right =
  false

indicator : Bool -> Nat
indicator true =
  suc zero
indicator false =
  zero

firstPeak : Nat -> Nat -> Nat
firstPeak current next =
  indicator (lessBool next current)

interiorPeak : Nat -> Nat -> Nat -> Nat
interiorPeak previous current next =
  indicator
    (andBool
      (lessBool previous current)
      (lessBool next current))

lastPeak : Nat -> Nat -> Nat
lastPeak previous current =
  indicator (lessBool previous current)

tailPeakCount :
  {bound remaining : Nat} ->
  Nat ->
  Nat ->
  Vec (Fin bound) remaining ->
  Nat
tailPeakCount previous current [] =
  lastPeak previous current
tailPeakCount previous current (next :: rest) =
  interiorPeak previous current (toNat next)
  + tailPeakCount current (toNat next) rest

localMaximumCount :
  {n : Nat} ->
  Vec (Fin n) n ->
  Nat
localMaximumCount {zero} [] =
  zero
localMaximumCount {suc zero} (x :: []) =
  suc zero
localMaximumCount {suc (suc n)} (x :: y :: rest) =
  firstPeak (toNat x) (toNat y)
  + tailPeakCount (toNat x) (toNat y) rest

IsPermutation :
  {n : Nat} ->
  Vec (Fin n) n ->
  Set
IsPermutation {n} entries =
  (i j : Fin n) ->
  lookup entries i == lookup entries j ->
  i == j

sumFin :
  {n : Nat} ->
  (Fin n -> Nat) ->
  Nat
sumFin {zero} term =
  zero
sumFin {suc n} term =
  term fzero
  + sumFin (\ i -> term (fsuc i))

oneN : Nat
oneN =
  suc zero

threeN : Nat
threeN =
  suc (suc (suc zero))

module Putnam2006A4Statement where

  PermutationVector : Nat -> Set
  PermutationVector n =
    Vec (Fin n) n

  totalLocalMaxima :
    {n permutationCount : Nat} ->
    HasCardinality
      (IsPermutation {n})
      permutationCount ->
    Nat
  totalLocalMaxima allPermutations =
    sumFin
      (\ i ->
        localMaximumCount
          (enumerate allPermutations i))

  proposition : Set
  proposition =
    (n : Nat) ->
    oneN <N n ->
    (permutationCount : Nat) ->
    (allPermutations :
      HasCardinality
        (IsPermutation {n})
        permutationCount) ->
    threeN
      * totalLocalMaxima allPermutations
    ==
    suc n * permutationCount

putnam-2006-a4 : Set
putnam-2006-a4 =
  Putnam2006A4Statement.proposition
