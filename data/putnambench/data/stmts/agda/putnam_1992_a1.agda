-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_a1:
-- an integer-valued function is n mapped to 1 - n exactly when it satisfies
-- the stated two functional equations and f(0) = 1.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

zeroZ : Int
zeroZ =
  pos zero

oneZ : Int
oneZ =
  pos (suc zero)

twoZ : Int
twoZ =
  pos (suc (suc zero))

putnam-1992-a1 : Set
putnam-1992-a1 =
  (f : Int -> Int) ->
  Iff
    ((n : Int) ->
      f n == subtractInt oneZ n)
    (((n : Int) ->
      f (f n) == n)
    and
    ((n : Int) ->
      f (addInt (f (addInt n twoZ)) twoZ) == n)
    and
    f zeroZ == oneZ)
