-- Statement-only formalization of PutnamBench corpus artifact putnam_1984_b1:
-- the factorial partial sums satisfy the recurrence with real polynomials
-- P(x) = x + 3 and Q(x) = -x - 2 for every positive index.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

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

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record Pair (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

open Pair

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R

    one-not-zero :
      oneR != zeroR

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) ->
      add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z ==
      multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x oneR == x
    multiply-zero :
      (x : R) -> multiply x zeroR == zeroR
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR == zeroR
    multiply-inverse :
      (x : R) ->
      x != zeroR ->
      multiply x (inverse x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqual x x
    order-transitive :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual y z ->
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqual x y ->
      lessOrEqual y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqual x y or lessOrEqual y x
    add-order :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and zeroR != oneR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) ->
      fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) ->
      fromNat m == fromNat n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) ->
            P x ->
            lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) ->
              P x ->
              lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open CompleteOrderedRealField

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

threeN : Nat
threeN =
  suc twoN

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

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

factorialSum : Nat -> Int
factorialSum zero =
  pos zero
factorialSum (suc n) =
  addInt
    (factorialSum n)
    (pos (factorial (suc n)))

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

data Polynomial (R : Set) : Set where
  constantPolynomial : R -> Polynomial R
  variablePolynomial : Polynomial R
  addPolynomial :
    Polynomial R ->
    Polynomial R ->
    Polynomial R
  negatePolynomial :
    Polynomial R ->
    Polynomial R
  multiplyPolynomial :
    Polynomial R ->
    Polynomial R ->
    Polynomial R

evaluatePolynomial :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Polynomial R ->
  R ->
  R
evaluatePolynomial reals (constantPolynomial c) x =
  c
evaluatePolynomial reals variablePolynomial x =
  x
evaluatePolynomial reals (addPolynomial p q) x =
  add reals
    (evaluatePolynomial reals p x)
    (evaluatePolynomial reals q x)
evaluatePolynomial reals (negatePolynomial p) x =
  negate reals (evaluatePolynomial reals p x)
evaluatePolynomial reals (multiplyPolynomial p q) x =
  multiply reals
    (evaluatePolynomial reals p x)
    (evaluatePolynomial reals q x)

solution :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Pair (Polynomial R) (Polynomial R)
solution reals =
  addPolynomial
    variablePolynomial
    (constantPolynomial (fromNat reals threeN))
  ,
  addPolynomial
    (negatePolynomial variablePolynomial)
    (constantPolynomial
      (negate reals (fromNat reals twoN)))

module Putnam1984B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  P : Polynomial R
  P =
    fst (solution reals)

  Q : Polynomial R
  Q =
    snd (solution reals)

  recurrence : (Nat -> Int) -> Set
  recurrence f =
    (n : Nat) ->
    oneN <=N n ->
    fromInt reals (f (n + twoN))
    ==
    add reals
      (multiply reals
        (evaluatePolynomial reals P (fromNat reals n))
        (fromInt reals (f (n + oneN))))
      (multiply reals
        (evaluatePolynomial reals Q (fromNat reals n))
        (fromInt reals (f n)))

  proposition : Set
  proposition =
    (f : Nat -> Int) ->
    ((n : Nat) ->
      oneN <=N n ->
      f n == factorialSum n) ->
    recurrence f

putnam-1984-b1 : Set1
putnam-1984-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1984B1Statement.proposition reals
