-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_a3:
-- digitwise replacement divisibility by 7 for two successive nine-digit
-- integer vectors forces corresponding endpoint digits to agree modulo 7.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<N_ _dividesZ_
infixr 3 _and_

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
  zero<sucN : {n : Nat} -> zero <N suc n
  suc<sucN  : {m n : Nat} -> m <N n -> suc m <N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

finEqual : {n : Nat} -> Fin n -> Fin n -> Bool
finEqual fzero fzero =
  true
finEqual fzero (fsuc j) =
  false
finEqual (fsuc i) fzero =
  false
finEqual (fsuc i) (fsuc j) =
  finEqual i j

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

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

record _dividesZ_ (divisor dividend : Int) : Set where
  field
    integer-quotient : Int
    integer-equation :
      dividend == multiplyInt divisor integer-quotient

oneN : Nat
oneN =
  suc zero

sevenN : Nat
sevenN =
  suc (suc (suc (suc (suc (suc oneN)))))

nineN : Nat
nineN =
  suc (suc sevenN)

tenN : Nat
tenN =
  suc nineN

powerNat : Nat -> Nat -> Nat
powerNat base zero =
  oneN
powerNat base (suc exponent) =
  powerNat base exponent * base

sumFin : {n : Nat} -> (Fin n -> Int) -> Int
sumFin {zero} terms =
  pos zero
sumFin {suc n} terms =
  addInt
    (terms fzero)
    (sumFin (\ i -> terms (fsuc i)))

Index : Set
Index =
  Fin nineN

Digits : Set
Digits =
  Index -> Int

data DecimalDigit : Int -> Set where
  decimal-digit :
    {n : Nat} ->
    n <N tenN ->
    DecimalDigit (pos n)

replaceDigit : Digits -> Digits -> Index -> Digits
replaceDigit d e replaced j with finEqual j replaced
... | true =
  e j
... | false =
  d j

digitsToNumberDefinition : Digits -> Int
digitsToNumberDefinition digits =
  sumFin
    (\ i ->
      multiplyInt
        (digits i)
        (pos (powerNat tenN (finToNat i))))

RelationMeaning :
  (Digits -> Int) ->
  Digits ->
  Digits ->
  Set
RelationMeaning digitsToNumber d e =
  ((i : Index) ->
    DecimalDigit (d i)
    and
    DecimalDigit (e i))
  and
  ((i : Index) ->
    pos sevenN dividesZ
    digitsToNumber (replaceDigit d e i))

putnam-1995-a3 : Set1
putnam-1995-a3 =
  (relation : Digits -> Digits -> Set) ->
  (digitsToNumber : Digits -> Int) ->
  digitsToNumber == digitsToNumberDefinition ->
  ((d e : Digits) ->
    Iff
      (relation d e)
      (RelationMeaning digitsToNumber d e)) ->
  (d e f : Digits) ->
  (relation d e and relation e f) ->
  (i : Index) ->
  pos sevenN dividesZ subtractInt (d i) (f i)
