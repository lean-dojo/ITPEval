-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_a4:
-- the recursively enumerated positive nonsquares have nth term equal to n plus
-- the nearest integer to the square root of n. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<=N_ _<N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

squareInt : Int -> Int
squareInt x =
  multiplyInt x x

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

fourN : Nat
fourN =
  twoN * twoN

oneZ : Int
oneZ =
  pos oneN

twoZ : Int
twoZ =
  pos twoN

IsIntegerSquare : Int -> Set
IsIntegerSquare x =
  Exists Int (\ m -> squareInt m == x)

RoundedSquareRoot : Nat -> Nat -> Set
RoundedSquareRoot n k =
  ((twoN * k - oneN) * (twoN * k - oneN) <=N fourN * n)
  and
  (fourN * n <N (twoN * k + oneN) * (twoN * k + oneN))

SatisfiesRecurrence : (Nat -> Int) -> Set
SatisfiesRecurrence a =
  (n : Nat) ->
  oneN <=N n ->
  (IsIntegerSquare (addInt (a n) oneZ)
    and
    a (suc n) == addInt (a n) twoZ)
  or
  (Not (IsIntegerSquare (addInt (a n) oneZ))
    and
    a (suc n) == addInt (a n) oneZ)

putnam-1966-a4 : Set
putnam-1966-a4 =
  (a : Nat -> Int) ->
  a oneN == twoZ ->
  SatisfiesRecurrence a ->
  (n : Nat) ->
  oneN <=N n ->
  Exists Nat
    (\ k ->
      RoundedSquareRoot n k
      and
      a n == pos (n + k))
