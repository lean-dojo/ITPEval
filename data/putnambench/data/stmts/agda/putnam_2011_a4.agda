-- Statement-only formalization of PutnamBench corpus artifact putnam_2011_a4
-- (putnambench__agda__putnam_2011_a4): positive sizes admitting a square
-- integer matrix with even row self-dot-products and odd dot-products between
-- distinct rows are exactly the odd sizes. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2011A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixl 6 _+Z_
infixl 7 _*Z_
infixr 3 _and_
infix 2 _iff_

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

record _iff_ (A B : Set) : Set where
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data OddNat : Nat -> Set where
  odd-one  : OddNat (suc zero)
  odd-step : {n : Nat} -> OddNat n -> OddNat (suc (suc n))

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

oneZ : Int
oneZ =
  pos (suc zero)

twoZ : Int
twoZ =
  pos (suc (suc zero))

EvenInt : Int -> Set
EvenInt value =
  Exists Int
    (\ half -> value == twoZ *Z half)

OddInt : Int -> Set
OddInt value =
  Exists Int
    (\ half -> value == (twoZ *Z half) +Z oneZ)

Matrix : Nat -> Set
Matrix n =
  Fin n -> Fin n -> Int

sumFinInt :
  {n : Nat} ->
  (Fin n -> Int) ->
  Int
sumFinInt {zero} terms =
  pos zero
sumFinInt {suc n} terms =
  terms fzero +Z
  sumFinInt (\ i -> terms (fsuc i))

rowDot :
  {n : Nat} ->
  Matrix n ->
  Fin n ->
  Fin n ->
  Int
rowDot {n} A leftRow rightRow =
  sumFinInt
    (\ column ->
      A leftRow column *Z A rightRow column)

RequiredRowParities :
  {n : Nat} ->
  Matrix n ->
  Set
RequiredRowParities {n} A =
  ((row : Fin n) ->
    EvenInt (rowDot A row row))
  and
  ((leftRow rightRow : Fin n) ->
    leftRow != rightRow ->
    OddInt (rowDot A leftRow rightRow))

AdmitsRequiredMatrix : Nat -> Set
AdmitsRequiredMatrix n =
  Exists (Matrix n) RequiredRowParities

putnam-2011-a4 : Set
putnam-2011-a4 =
  (n : Nat) ->
  Positive n ->
  AdmitsRequiredMatrix n iff OddNat n
