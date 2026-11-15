-- Statement-only formalization of PutnamBench corpus artifact putnam_2014_b3
-- (putnambench__agda__putnam_2014_b3): a rational matrix with at least m+n
-- distinct primes among its absolute entry values has rank at least two. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2014B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixl 7 _*Z_

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

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

Divides : Nat -> Nat -> Set
Divides divisor number =
  Exists Nat
    (\ factor -> divisor * factor == number)

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

infixr 2 _or_

Prime : Nat -> Set
Prime number =
  two <=N number
  and
  ((divisor : Nat) ->
    Divides divisor number ->
    divisor == one or divisor == number)

negativeNat : Nat -> Int
negativeNat zero =
  pos zero
negativeNat (suc n) =
  negsuc n

_*Z_ : Int -> Int -> Int
pos m *Z pos n =
  pos (m * n)
pos m *Z negsuc n =
  negativeNat (m * suc n)
negsuc m *Z pos n =
  negativeNat (suc m * n)
negsuc m *Z negsuc n =
  pos (suc m * suc n)

intMagnitude : Int -> Nat
intMagnitude (pos n) =
  n
intMagnitude (negsuc n) =
  suc n

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

AbsoluteEqualsNat : Rational -> Nat -> Set
AbsoluteEqualsNat q n =
  intMagnitude (numerator q) == n * denominator q

Matrix : Nat -> Nat -> Set
Matrix m n =
  Fin m -> Fin n -> Rational

record AtLeastDistinctPrimeEntries
  {m n : Nat}
  (A : Matrix m n) :
  Set where

  field
    prime-values :
      Fin (m + n) ->
      Nat
    values-prime :
      (k : Fin (m + n)) ->
      Prime (prime-values k)
    values-occur :
      (k : Fin (m + n)) ->
      Exists (Fin m)
        (\ i ->
          Exists (Fin n)
            (\ j ->
              AbsoluteEqualsNat (A i j) (prime-values k)))
    values-injective :
      (k l : Fin (m + n)) ->
      prime-values k == prime-values l ->
      k == l

RationalProductsEqual :
  Rational ->
  Rational ->
  Rational ->
  Rational ->
  Set
RationalProductsEqual x y u v =
  (numerator x *Z numerator y)
    *Z pos (denominator u * denominator v)
  ==
  (numerator u *Z numerator v)
    *Z pos (denominator x * denominator y)

record RankAtLeastTwo
  {m n : Nat}
  (A : Matrix m n) :
  Set where

  field
    first-row second-row :
      Fin m
    first-column second-column :
      Fin n
    distinct-rows :
      first-row != second-row
    distinct-columns :
      first-column != second-column
    nonzero-minor :
      Not
        (RationalProductsEqual
          (A first-row first-column)
          (A second-row second-column)
          (A first-row second-column)
          (A second-row first-column))

Positive : Nat -> Set
Positive n =
  one <=N n

putnam-2014-b3 : Set
putnam-2014-b3 =
  (m n : Nat) ->
  (A : Matrix m n) ->
  Positive m and Positive n ->
  AtLeastDistinctPrimeEntries A ->
  RankAtLeastTwo A
