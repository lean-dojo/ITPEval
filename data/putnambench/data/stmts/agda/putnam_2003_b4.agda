-- Statement-only formalization of PutnamBench corpus artifact putnam_2003_b4
-- (putnambench__agda__putnam_2003_b4): rationality of the product of two
-- roots of a quartic with integer coefficients under a rational root-sum
-- hypothesis. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))
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

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

power :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
power reals x zero =
  oneR reals
power reals x (suc n) =
  multiply reals x (power reals x n)

quarticValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  Int ->
  Int ->
  Int ->
  Int ->
  R ->
  R
quarticValue reals a b c d e z =
  add reals
    (add reals
      (add reals
        (add reals
          (multiply reals (fromInt reals a) (power reals z 4))
          (multiply reals (fromInt reals b) (power reals z 3)))
        (multiply reals (fromInt reals c) (power reals z 2)))
      (multiply reals (fromInt reals d) z))
    (fromInt reals e)

factorizedValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R ->
  R ->
  R ->
  R ->
  R ->
  R
factorizedValue reals a r1 r2 r3 r4 z =
  multiply reals
    (multiply reals
      (multiply reals
        (multiply reals
          (fromInt reals a)
          (subtract reals z r1))
        (subtract reals z r2))
      (subtract reals z r3))
    (subtract reals z r4)

IsRational :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
IsRational reals x =
  Exists Int
    (\ numerator ->
      Exists Int
        (\ denominator ->
          denominator != pos zero
          and
          x ==
          divide reals
            (fromInt reals numerator)
            (fromInt reals denominator)))

putnam-2003-b4 : Set1
putnam-2003-b4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (f : R -> R) ->
  (a b c d e : Int) ->
  (r1 r2 r3 r4 : R) ->
  a != pos zero ->
  ((z : R) ->
    f z == quarticValue reals a b c d e z) ->
  ((z : R) ->
    f z == factorizedValue reals a r1 r2 r3 r4 z) ->
  (IsRational reals (add reals r1 r2)
  and
  add reals r1 r2 != add reals r3 r4) ->
  IsRational reals (multiply reals r1 r2)
