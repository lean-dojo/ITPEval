-- Statement-only formalization of PutnamBench corpus artifact putnam_2012_a4
-- (putnambench__agda__putnam_2012_a4): an interval length-product bound makes
-- the selected integers the intersection of an interval with a finite
-- arithmetic progression. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2012A4 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

finToNat : {n : Nat} -> Fin n -> Nat
finToNat fzero =
  zero
finToNat (fsuc i) =
  suc (finToNat i)

finToInt : {n : Nat} -> Fin n -> Int
finToInt i =
  pos (finToNat i)

data PositiveInt : Int -> Set where
  positive : {n : Nat} -> PositiveInt (pos (suc n))

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

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

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
        (\ n ->
          lessOrEqual x (fromNat n))
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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

record Interval (R : Set) : Set where
  constructor endpoints
  field
    lower upper : R

open Interval

InClosedInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Interval R ->
  R ->
  Set
InClosedInterval reals I x =
  lessOrEqual reals (lower I) x
  and
  lessOrEqual reals x (upper I)

IntervalNondegenerate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Interval R ->
  Set
IntervalNondegenerate reals I =
  StrictLess reals (lower I) (upper I)

intervalLength :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Interval R ->
  R
intervalLength reals I =
  subtract reals (upper I) (lower I)

SameSet :
  (Int -> Set) ->
  (Int -> Set) ->
  Set
SameSet X Y =
  (x : Int) ->
  X x iff Y x

FiniteArithmeticProgression :
  (Int -> Set) ->
  Set
FiniteArithmeticProgression X =
  Exists Nat
    (\ n ->
      Exists Int
        (\ firstTerm ->
          Exists Int
            (\ differenceTerm ->
              PositiveInt differenceTerm
              and
              SameSet X
                (\ x ->
                  Exists (Fin n)
                    (\ i ->
                      x ==
                      addInt firstTerm
                        (multiplyInt
                          (finToInt i)
                          differenceTerm))))))

module Putnam2012A4Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  T :
    Int ->
    Interval R ->
    Int ->
    Set
  T q B x =
    Exists Int
      (\ b ->
        Exists Int
          (\ m ->
            InClosedInterval reals B (fromInt reals b)
            and
            x == addInt b (multiplyInt m q)))

  S :
    Int ->
    Int ->
    Interval R ->
    Interval R ->
    Int ->
    Set
  S q r A B a =
    InClosedInterval reals A (fromInt reals a)
    and
    T q B (multiplyInt r a)

  RelevantSet :
    Int ->
    Int ->
    Interval R ->
    Interval R ->
    Int ->
    Set
  RelevantSet q r A B x =
    S q r A B x
    and
    InClosedInterval reals A (fromInt reals x)

  LengthProductBelow :
    Int ->
    Interval R ->
    Interval R ->
    Set
  LengthProductBelow q A B =
    StrictLess reals
      (multiply reals
        (intervalLength reals A)
        (intervalLength reals B))
      (fromInt reals q)

  proposition : Set
  proposition =
    (q r : Int) ->
    (A B : Interval R) ->
    PositiveInt q ->
    IntervalNondegenerate reals A
    and
    IntervalNondegenerate reals B ->
    LengthProductBelow q A B ->
    FiniteArithmeticProgression
      (RelevantSet q r A B)

putnam-2012-a4 : Set1
putnam-2012-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2012A4Statement.proposition reals
