-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_a4:
-- an irreducible integer cubic with roots related by a unit translation has
-- another root equal to one of two explicit rational functions. This file
-- contains no proof.

{-# OPTIONS --safe #-}

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

record CompleteOrderedField (R : Set) : Set1 where
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

open CompleteOrderedField

fromInt :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

cube :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
cube reals x =
  multiply reals (square reals x) x

cubicMinusOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  Int ->
  R ->
  R
cubicMinusOne reals a b x =
  add reals
    (add reals
      (add reals
        (cube reals x)
        (multiply reals
          (fromInt reals a)
          (square reals x)))
      (multiply reals (fromInt reals b) x))
    (negate reals (oneR reals))

cubicPlusOne :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  Int ->
  R ->
  R
cubicPlusOne reals c d x =
  add reals
    (add reals
      (add reals
        (cube reals x)
        (multiply reals
          (fromInt reals c)
          (square reals x)))
      (multiply reals (fromInt reals d) x))
    (oneR reals)

IsRational :
  {R : Set} ->
  CompleteOrderedField R ->
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

IrreducibleCubic :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  Int ->
  Set
IrreducibleCubic {R} reals a b =
  (x : R) ->
  IsRational reals x ->
  Not (cubicMinusOne reals a b x == zeroR reals)

firstSolution :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
firstSolution reals r =
  negate reals
    (divide reals
      (oneR reals)
      (add reals r (oneR reals)))

secondSolution :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
secondSolution reals r =
  negate reals
    (divide reals
      (add reals r (oneR reals))
      r)

putnam-1976-a4 : Set1
putnam-1976-a4 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (a b c d : Int) ->
  (r : R) ->
  (cubicMinusOne reals a b r == zeroR reals
    and
    IrreducibleCubic reals a b) ->
  cubicPlusOne reals c d
    (add reals r (oneR reals))
    ==
    zeroR reals ->
  Exists R
    (\ s ->
      cubicMinusOne reals a b s == zeroR reals
      and
      (s == firstSolution reals r
        or
        s == secondSolution reals r))
