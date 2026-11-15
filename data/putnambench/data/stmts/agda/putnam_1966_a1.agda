-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_a1:
-- for positive integers x > y, the difference of the inclusive partial sums
-- of floor(n / 2) at x + y and x - y equals x * y. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

infix 4 _<_

data _<_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero < suc n
  suc<suc  : {m n : Nat} -> m < n -> suc m < suc n

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

half : Nat -> Nat
half zero =
  zero
half (suc zero) =
  zero
half (suc (suc n)) =
  suc (half n)

sumThrough : Nat -> (Nat -> Nat) -> Nat
sumThrough zero term =
  term zero
sumThrough (suc n) term =
  sumThrough n term + term (suc n)

f : Nat -> Int
f n =
  pos (sumThrough n half)

putnam-1966-a1 : Set
putnam-1966-a1 =
  (x y : Nat) ->
  zero < x ->
  zero < y ->
  y < x ->
  pos (x * y) == subtractInt (f (x + y)) (f (x - y))
