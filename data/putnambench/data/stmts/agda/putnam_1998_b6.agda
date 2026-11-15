-- Statement-only formalization of PutnamBench corpus artifact putnam_1998_b6
-- (putnambench__agda__putnam_1998_b6): every integer-coefficient monic cubic
-- takes a non-square value at some positive integer. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixl 6 _+Z_
infixl 7 _*Z_
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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negative (m * suc n)
negsuc m *Z pos n =
  negative (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

data PositiveInteger : Int -> Set where
  positive : {n : Nat} -> PositiveInteger (pos (suc n))

cubicValue : Int -> Int -> Int -> Int -> Int
cubicValue a b c n =
  n *Z n *Z n +Z a *Z n *Z n +Z b *Z n +Z c

NotIntegerSquare : Int -> Set
NotIntegerSquare value =
  (m : Int) ->
  value != m *Z m

putnam-1998-b6 : Set
putnam-1998-b6 =
  (a b c : Int) ->
  Exists Int
    (\ n ->
      PositiveInteger n
      and
      NotIntegerSquare (cubicValue a b c n))
