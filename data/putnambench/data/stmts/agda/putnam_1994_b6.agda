-- Statement-only formalization of PutnamBench corpus artifact putnam_1994_b6
-- (putnambench__agda__putnam_1994_b6): the values 101a - 100 times 2^a,
-- for indices from 0 through 99, have pairwise sums unique modulo 10100 up
-- to exchanging the two indices. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _dividesZ_
infixr 3 _and_
infixr 2 _or_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
    quotient : Int
    division-equation :
      dividend == multiplyInt divisor quotient

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

powerOfTwo : Nat -> Nat
powerOfTwo zero =
  oneN
powerOfTwo (suc exponent) =
  twoN * powerOfTwo exponent

sequenceValue : Nat -> Int
sequenceValue a =
  subtractInt
    (multiplyInt (pos 101) (pos a))
    (multiplyInt (pos 100) (pos (powerOfTwo a)))

CongruentModulo : Nat -> Int -> Int -> Set
CongruentModulo modulus leftValue rightValue =
  pos modulus dividesZ subtractInt leftValue rightValue

UnorderedPairEqual : Nat -> Nat -> Nat -> Nat -> Set
UnorderedPairEqual a b c d =
  (a == c and b == d) or (a == d and b == c)

putnam-1994-b6 : Set
putnam-1994-b6 =
  (n : Nat -> Int) ->
  ((a : Nat) -> n a == sequenceValue a) ->
  (a b c d : Nat) ->
  a <=N 99 ->
  b <=N 99 ->
  c <=N 99 ->
  d <=N 99 ->
  CongruentModulo
    10100
    (addInt (n a) (n b))
    (addInt (n c) (n d)) ->
  UnorderedPairEqual a b c d
