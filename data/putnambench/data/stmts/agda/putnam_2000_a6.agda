-- Statement-only formalization of PutnamBench corpus artifact putnam_2000_a6:
-- an integer polynomial iterated from zero can return to zero at a positive
-- index only if its first or second iterate is zero. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

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

Polynomial : Set
Polynomial =
  List Int

evaluatePolynomial : Polynomial -> Int -> Int
evaluatePolynomial [] x =
  pos zero
evaluatePolynomial (coefficient ∷ coefficients) x =
  addInt coefficient
    (multiplyInt x (evaluatePolynomial coefficients x))

putnam-2000-a6 : Set
putnam-2000-a6 =
  (f : Polynomial) ->
  (a : Nat -> Int) ->
  a zero == pos zero ->
  ((n : Nat) ->
    a (suc n) == evaluatePolynomial f (a n)) ->
  Exists Nat
    (\ m ->
      Positive m
      and
      a m == pos zero) ->
  (a (suc zero) == pos zero)
  or
  (a (suc (suc zero)) == pos zero)
