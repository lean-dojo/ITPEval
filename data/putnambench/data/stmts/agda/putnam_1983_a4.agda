-- Statement-only formalization of PutnamBench corpus artifact putnam_1983_a4:
-- for positive natural k and m = 6k - 1, the alternating integer sum of
-- binomial coefficients indexed from 1 through 2k - 1 is nonzero.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<_ _!=_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

six : Nat
six =
  three + three

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

powerInt : Int -> Nat -> Int
powerInt x zero =
  pos one
powerInt x (suc n) =
  multiplyInt x (powerInt x n)

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc r) =
  zero
choose (suc n) (suc r) =
  choose n (suc r) + choose n r

sumFromOneThroughInt : Nat -> (Nat -> Int) -> Int
sumFromOneThroughInt zero term =
  pos zero
sumFromOneThroughInt (suc n) term =
  addInt
    (sumFromOneThroughInt n term)
    (term (suc n))

alternatingBinomialSum : Nat -> Nat -> Int
alternatingBinomialSum m k =
  sumFromOneThroughInt (two * k - one)
    (\ j ->
      multiplyInt
        (powerInt (negsuc zero) (j + one))
        (pos (choose m (three * j - one))))

putnam-1983-a4 : Set
putnam-1983-a4 =
  (k m : Nat) ->
  (S : Int) ->
  zero < k ->
  m == (six * k - one) ->
  S == alternatingBinomialSum m k ->
  S != pos zero
