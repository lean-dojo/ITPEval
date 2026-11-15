-- Statement-only formalization of PutnamBench corpus artifact putnam_1995_b3
-- (putnambench__agda__putnam_1995_b3): the sum of the determinants of the
-- n by n digit matrices associated with all n-squared-digit decimal integers.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

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
toNat (fsuc i) =
  suc (toNat i)

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

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

sumFin : {n : Nat} -> (Fin n -> Int) -> Int
sumFin {zero} term =
  pos zero
sumFin {suc n} term =
  addInt
    (term fzero)
    (sumFin (\ i -> term (fsuc i)))

Matrix : Nat -> Set
Matrix n =
  Fin n -> Fin n -> Int

skip :
  {n : Nat} ->
  Fin (suc n) ->
  Fin n ->
  Fin (suc n)
skip {zero} removed ()
skip {suc n} fzero i =
  fsuc i
skip {suc n} (fsuc removed) fzero =
  fzero
skip {suc n} (fsuc removed) (fsuc i) =
  fsuc (skip removed i)

firstRowMinor :
  {n : Nat} ->
  Matrix (suc n) ->
  Fin (suc n) ->
  Matrix n
firstRowMinor A removedColumn i j =
  A (fsuc i) (skip removedColumn j)

alternatingSign :
  {n : Nat} ->
  Fin n ->
  Int
alternatingSign fzero =
  pos (suc zero)
alternatingSign (fsuc i) =
  negateInt (alternatingSign i)

determinant :
  {n : Nat} ->
  Matrix n ->
  Int
determinant {zero} A =
  pos (suc zero)
determinant {suc n} A =
  sumFin
    (\ column ->
      multiplyInt
        (alternatingSign column)
        (multiplyInt
          (A fzero column)
          (determinant (firstRowMinor A column))))

square : Nat -> Nat
square n =
  n * n

nine : Nat
nine =
  9

record ValidDigits (n : Nat) (digits : Nat -> Nat) : Set where
  field
    leading-digit-nonzero :
      digits zero != zero

    decimal-digits :
      (i : Fin (square n)) ->
      digits (toNat i) <=N nine

    zero-after-n-squared :
      (i : Nat) ->
      square n <=N i ->
      digits i == zero

DigitFunctionEqual :
  (Nat -> Nat) ->
  (Nat -> Nat) ->
  Set
DigitFunctionEqual left right =
  (i : Nat) ->
  left i == right i

digitsToMatrix :
  (n : Nat) ->
  (Nat -> Nat) ->
  Matrix n
digitsToMatrix n digits i j =
  pos (digits (toNat i * n + toNat j))

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record HasExtensionalFiniteSum
  {A : Set}
  (equivalent : A -> A -> Set)
  (member : A -> Set)
  (term : A -> Int)
  (total : Int) :
  Set where

  field
    cardinality :
      Nat

    enumerate :
      Fin cardinality ->
      A

    enumerated-member :
      (index : Fin cardinality) ->
      member (enumerate index)

    enumeration-complete :
      (item : A) ->
      member item ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))

    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

    sum-is-total :
      sumFin (\ index -> term (enumerate index)) == total

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

ten : Nat
ten =
  10

fortyFive : Nat
fortyFive =
  45

equalNat : Nat -> Nat -> Bool
equalNat zero zero =
  true
equalNat zero (suc n) =
  false
equalNat (suc m) zero =
  false
equalNat (suc m) (suc n) =
  equalNat m n

putnam-1995-b3-solution : Nat -> Int
putnam-1995-b3-solution n with equalNat n one
... | true =
  pos fortyFive
... | false with equalNat n two
...   | true =
  pos (ten * fortyFive * fortyFive)
...   | false =
  pos zero

putnam-1995-b3 : Set
putnam-1995-b3 =
  (n : Nat) ->
  Positive n ->
  HasExtensionalFiniteSum
    DigitFunctionEqual
    (ValidDigits n)
    (\ digits -> determinant (digitsToMatrix n digits))
    (putnam-1995-b3-solution n)
