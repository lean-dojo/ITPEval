-- Statement-only formalization of PutnamBench corpus artifact putnam_2013_a4
-- (putnambench__agda__putnam_2013_a4): balanced zero counts on equal-length
-- arcs of a finite binary circle force an arc realizing both integral average
-- digit counts. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2013A4 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_
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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat fzero =
  zero
toNat (fsuc index) =
  suc (toNat index)

record Arc (n : Nat) : Set where
  constructor arc
  field
    start  : Fin n
    length : Fin (suc n)

open Arc

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

subtractInt : Int -> Int -> Int
subtractInt x y =
  addInt x (negateInt y)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

absoluteValue : Int -> Nat
absoluteValue (pos n) =
  n
absoluteValue (negsuc n) =
  suc n

sumFinInt :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
sumFinInt {zero} term =
  pos zero
sumFinInt {suc n} term =
  addInt
    (term fzero)
    (sumFinInt (\ index -> term (fsuc index)))

sameBool : Bool -> Bool -> Bool
sameBool false false =
  true
sameBool false true =
  false
sameBool true false =
  false
sameBool true true =
  true

indicator : Bool -> Bool -> Int
indicator actual expected with sameBool actual expected
... | false =
  pos zero
... | true =
  pos (suc zero)

countDigit :
  (Nat -> Bool) ->
  Bool ->
  Nat ->
  Nat ->
  Int
countDigit circle digit start-index zero =
  pos zero
countDigit circle digit start-index (suc remaining) =
  addInt
    (indicator (circle start-index) digit)
    (countDigit circle digit (suc start-index) remaining)

ArcCount :
  {n : Nat} ->
  (Nat -> Bool) ->
  Bool ->
  Arc n ->
  Int
ArcCount circle digit w =
  countDigit
    circle
    digit
    (toNat (start w))
    (toNat (length w))

Periodic : (Nat -> Bool) -> Nat -> Set
Periodic circle period =
  (index : Nat) ->
  circle (index + period) == circle index

CorrectCounts :
  {n : Nat} ->
  (Nat -> Bool) ->
  (Arc n -> Int) ->
  (Arc n -> Int) ->
  Set
CorrectCounts circle Z N =
  ((w : Arc _) -> Z w == ArcCount circle false w)
  and
  ((w : Arc _) -> N w == ArcCount circle true w)

BalancedZeroCounts :
  {n : Nat} ->
  (Arc n -> Int) ->
  Set
BalancedZeroCounts Z =
  (w w' : Arc _) ->
  length w == length w' ->
  absoluteValue (subtractInt (Z w) (Z w')) <=N suc zero

IntegralAverages :
  {n k : Nat} ->
  (Arc n -> Int) ->
  (Arc n -> Int) ->
  (Fin k -> Arc n) ->
  Int ->
  Int ->
  Set
IntegralAverages {k = k} Z N ws Zsum Nsum =
  (multiplyInt (pos k) Zsum ==
    sumFinInt (\ index -> Z (ws index)))
  and
  (multiplyInt (pos k) Nsum ==
    sumFinInt (\ index -> N (ws index)))

RealizesAverages :
  {n : Nat} ->
  (Arc n -> Int) ->
  (Arc n -> Int) ->
  Int ->
  Int ->
  Set
RealizesAverages {n} Z N Zsum Nsum =
  Exists (Arc n)
    (\ w ->
      (Z w == Zsum)
      and
      (N w == Nsum))

putnam-2013-a4 : Set
putnam-2013-a4 =
  (n k : Nat) ->
  Positive n ->
  Positive k ->
  (circle : Nat -> Bool) ->
  Periodic circle n ->
  (Z N : Arc n -> Int) ->
  (ws : Fin k -> Arc n) ->
  (Zsum Nsum : Int) ->
  CorrectCounts circle Z N ->
  BalancedZeroCounts Z ->
  IntegralAverages Z N ws Zsum Nsum ->
  RealizesAverages Z N Zsum Nsum
