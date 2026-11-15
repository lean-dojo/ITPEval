-- Statement-only formalization of PutnamBench corpus artifact putnam_2015_b5
-- (putnambench__agda__putnam_2015_b5): the integer recurrence expression for
-- counts of permutations with bounded images of adjacent entries equals 4.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2015B5 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)

infix 4 _<=N_
infixl 6 _+Z_ _-Z_

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc index) =
  suc (finToNat index)

natDistance : Nat -> Nat -> Nat
natDistance m n =
  (m - n) + (n - m)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

three : Nat
three =
  suc two

four : Nat
four =
  suc three

five : Nat
five =
  suc four

record IsBijective
  {A B : Set}
  (function : A -> B) :
  Set where

  field
    injective :
      (left right : A) ->
      function left == function right ->
      left == right
    surjective :
      (output : B) ->
      Exists A
        (\ input -> function input == output)

record ValidPermutation (n : Nat) : Set where
  field
    apply :
      Fin n ->
      Fin n
    bijective :
      IsBijective apply
    adjacent-image-bound :
      (i j : Fin n) ->
      natDistance (finToNat i) (finToNat j) == one ->
      natDistance (finToNat (apply i)) (finToNat (apply j)) <=N two

SameValidPermutation :
  {n : Nat} ->
  ValidPermutation n ->
  ValidPermutation n ->
  Set
SameValidPermutation {n} left right =
  (index : Fin n) ->
  ValidPermutation.apply left index ==
  ValidPermutation.apply right index

record HasExtensionalCardinality
  {A : Set}
  (equivalent : A -> A -> Set)
  (cardinality : Nat) :
  Set where

  field
    enumerate :
      Fin cardinality ->
      A
    enumeration-complete :
      (item : A) ->
      Exists (Fin cardinality)
        (\ index -> equivalent item (enumerate index))
    enumeration-injective :
      (left-index right-index : Fin cardinality) ->
      equivalent (enumerate left-index) (enumerate right-index) ->
      left-index == right-index

CountsValidPermutations :
  (Nat -> Nat) ->
  Set
CountsValidPermutations P =
  (n : Nat) ->
  HasExtensionalCardinality
    {A = ValidPermutation n}
    SameValidPermutation
    (P n)

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

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

_+Z_ : Int -> Int -> Int
pos m +Z pos n =
  pos (m + n)
pos m +Z negsuc n =
  difference m (suc n)
negsuc m +Z pos n =
  difference n (suc m)
negsuc m +Z negsuc n =
  negsuc (suc (m + n))

_-Z_ : Int -> Int -> Int
x -Z y =
  x +Z negateInt y

recurrenceExpression :
  (Nat -> Nat) ->
  Nat ->
  Int
recurrenceExpression P n =
  ((pos (P (n + five)) -Z pos (P (n + four)))
    -Z pos (P (n + three)))
  +Z pos (P n)

putnam-2015-b5 : Set
putnam-2015-b5 =
  (P : Nat -> Nat) ->
  CountsValidPermutations P ->
  (n : Nat) ->
  two <=N n ->
  recurrenceExpression P n == pos four
