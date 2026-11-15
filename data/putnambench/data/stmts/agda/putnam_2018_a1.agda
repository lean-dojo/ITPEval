-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_a1
-- (putnambench__agda__putnam_2018_a1): the positive integer solutions of
-- 1/a + 1/b = 3/2018 are exactly the six listed ordered pairs.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018A1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

infix 4 _==Q_
infixr 3 _and_
infixr 2 _or_
infix 1 _iff_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

record Fraction : Set where
  constructor fraction
  field
    numerator   : Nat
    denominator : Nat

open Fraction

_==Q_ : Fraction -> Fraction -> Set
p ==Q q =
  numerator p * denominator q ==
  numerator q * denominator p

reciprocal-sum-equation : Nat -> Nat -> Set
reciprocal-sum-equation a b =
  fraction (b + a) (a * b) ==Q fraction 3 2018

putnam-2018-a1-solution : Nat -> Nat -> Set
putnam-2018-a1-solution a b =
  (a == 673 and b == 1358114) or
  (a == 674 and b == 340033) or
  (a == 1009 and b == 2018) or
  (a == 2018 and b == 1009) or
  (a == 340033 and b == 674) or
  (a == 1358114 and b == 673)

putnam-2018-a1 : Set
putnam-2018-a1 =
  (a b : Nat) ->
  Positive a ->
  Positive b ->
  reciprocal-sum-equation a b iff
  putnam-2018-a1-solution a b
