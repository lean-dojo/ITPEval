-- Statement-only formalization of PutnamBench corpus artifact putnam_2009_b1
-- (putnambench__agda__putnam_2009_b1): every positive rational is a quotient
-- of finite products of factorials of primes. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2009B1 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<=N_
infixr 3 _and_
infixr 2 _or_

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

Prime : Nat -> Set
Prime number =
  two <=N number
  and
  ((divisor : Nat) ->
    Divides divisor number ->
    divisor == one or divisor == number)

data All {A : Set} (P : A -> Set) : List A -> Set where
  all[]  : All P []
  all∷   : {x : A} {xs : List A} -> P x -> All P xs -> All P (x ∷ xs)

factorial : Nat -> Nat
factorial zero =
  one
factorial (suc n) =
  suc n * factorial n

factorialProduct : List Nat -> Nat
factorialProduct [] =
  one
factorialProduct (n ∷ ns) =
  factorial n * factorialProduct ns

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

scaleInt : Int -> Nat -> Int
scaleInt (pos magnitude) factor =
  pos (magnitude * factor)
scaleInt (negsuc magnitude) factor =
  negative (suc magnitude * factor)

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

data PositiveInt : Int -> Set where
  positive : {n : Nat} -> PositiveInt (pos (suc n))

PositiveRational : Rational -> Set
PositiveRational q =
  PositiveInt (numerator q)

RepresentsFactorialQuotient :
  List Nat ->
  List Nat ->
  Rational ->
  Set
RepresentsFactorialQuotient numerator-primes denominator-primes q =
  pos
    (factorialProduct numerator-primes * denominator q)
  ==
  scaleInt
    (numerator q)
    (factorialProduct denominator-primes)

putnam-2009-b1 : Set
putnam-2009-b1 =
  (q : Rational) ->
  PositiveRational q ->
  Exists (List Nat)
    (\ numerator-primes ->
      Exists (List Nat)
        (\ denominator-primes ->
          All Prime numerator-primes
          and
          All Prime denominator-primes
          and
          RepresentsFactorialQuotient
            numerator-primes
            denominator-primes
            q))
