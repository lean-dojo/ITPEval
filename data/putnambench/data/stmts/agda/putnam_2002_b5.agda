-- Statement-only formalization of PutnamBench corpus artifact putnam_2002_b5:
-- some natural number is a three-digit palindrome in at least 2002 distinct
-- natural-number bases. This file contains no proof.

{-# OPTIONS --safe #-}

module putnam-2002-b5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=_ _<_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data _<=_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <= n
  suc<=suc : {m n : Nat} -> m <= n -> suc m <= suc n

_<_ : Nat -> Nat -> Set
m < n =
  suc m <= n

one : Nat
one =
  suc zero

record ThreeDigitPalindrome (base number : Nat) : Set where
  field
    base-at-least-one : one <= base
    outer-digit       : Nat
    middle-digit      : Nat
    outer-positive    : zero < outer-digit
    outer-below-base  : outer-digit < base
    middle-below-base : middle-digit < base
    base-expansion    :
      number
      ==
      outer-digit
      + base * middle-digit
      + (base * base) * outer-digit

record AtLeastPalindromicBases (number count : Nat) : Set where
  field
    base :
      Fin count ->
      Nat
    palindromic :
      (index : Fin count) ->
      ThreeDigitPalindrome (base index) number
    distinct :
      (left-index right-index : Fin count) ->
      base left-index == base right-index ->
      left-index == right-index

putnam-2002-b5 : Set
putnam-2002-b5 =
  Exists Nat
    (\ number ->
      AtLeastPalindromicBases number 2002)
