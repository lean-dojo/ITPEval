-- Statement-only formalization of PutnamBench corpus artifact putnam_1971_a5:
-- positive integer solitaire scores a > b have exactly 35 unattainable
-- accumulated totals including 58 exactly when (a , b) = (11 , 8).
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_ _<N_ _<Z_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc  : {m n : Nat} -> m <N n -> suc m <N suc n

data _<Z_ : Int -> Int -> Set where
  neg<pos : {m n : Nat} -> negsuc m <Z pos n
  pos<pos : {m n : Nat} -> m <N n -> pos m <Z pos n
  neg<neg : {m n : Nat} -> n <N m -> negsuc m <Z negsuc n

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

scaleNat : Nat -> Int -> Int
scaleNat zero x =
  pos zero
scaleNat (suc n) x =
  addInt x (scaleNat n x)

score : Int -> Int -> Nat -> Nat -> Int
score x y m n =
  addInt (scaleNat m x) (scaleNat n y)

Unattainable : Int -> Int -> Nat -> Set
Unattainable x y s =
  Not
    (Exists Nat
      (\ m ->
        Exists Nat
          (\ n -> score x y m n == pos s)))

thirtyFive : Nat
thirtyFive =
  35

fiftyEight : Nat
fiftyEight =
  58

ScoreCondition : Int -> Int -> Set
ScoreCondition x y =
  HasCardinality (Unattainable x y) thirtyFive
  and
  Unattainable x y fiftyEight

elevenInt : Int
elevenInt =
  pos 11

eightInt : Int
eightInt =
  pos 8

putnam-1971-a5 : Set1
putnam-1971-a5 =
  (a b : Int) ->
  (PositiveInteger a and PositiveInteger b and b <Z a) ->
  (pab : Int -> Int -> Set) ->
  ((x y : Int) ->
    Iff
      (pab x y)
      (ScoreCondition x y)) ->
  Iff
    (pab a b)
    (a == elevenInt and b == eightInt)
