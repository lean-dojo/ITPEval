-- Statement-only formalization of PutnamBench corpus artifact putnam_2018_a6
-- (putnambench__agda__putnam_2018_a6): four points in the real Euclidean
-- plane with no three collinear and rational squared pairwise distances have
-- a rational quotient of the areas of triangles ABC and ABD. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module Putnam2018A6 where

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
    negate inverse squareRoot : R -> R
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

    square-root-nonnegative :
      (x : R) ->
      lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) ->
      lessOrEqual zeroR x ->
      multiply (squareRoot x) (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual x zeroR ->
      squareRoot x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqual zeroR y ->
      multiply y y == x ->
      y == squareRoot x

open CompleteOrderedRealField

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

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

fromInt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

record Rational : Set where
  constructor fraction
  field
    numerator             : Int
    denominator-minus-one : Nat

open Rational

denominator : Rational -> Nat
denominator q =
  suc (denominator-minus-one q)

rationalValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Rational ->
  R
rationalValue reals q =
  divide reals
    (fromInt reals (numerator q))
    (fromNat reals (denominator q))

IsRational :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
IsRational reals x =
  Exists Rational
    (\ q -> x == rationalValue reals q)

twoN : Nat
twoN =
  suc (suc zero)

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  inverse reals (fromNat reals twoN)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

doubleSignedArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
doubleSignedArea reals a b c =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiply reals
      (subtract reals (y-coordinate b) (y-coordinate a))
      (subtract reals (x-coordinate c) (x-coordinate a)))

Collinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Collinear reals a b c =
  doubleSignedArea reals a b c == zeroR reals

triangleArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
triangleArea reals a b c =
  multiply reals
    (half reals)
    (squareRoot reals
      (square reals (doubleSignedArea reals a b c)))

module Putnam2018A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  PairHasRationalSquaredDistance :
    Point R ->
    Point R ->
    Set
  PairHasRationalSquaredDistance p q =
    p != q
    and
    IsRational reals (squaredDistance reals p q)

  GeneralPosition :
    Point R ->
    Point R ->
    Point R ->
    Point R ->
    Set
  GeneralPosition A B C D =
    Not (Collinear reals A B C)
    and
    Not (Collinear reals A B D)
    and
    Not (Collinear reals A C D)
    and
    Not (Collinear reals B C D)

  AllSquaredDistancesRational :
    Point R ->
    Point R ->
    Point R ->
    Point R ->
    Set
  AllSquaredDistancesRational A B C D =
    PairHasRationalSquaredDistance A B
    and
    PairHasRationalSquaredDistance A C
    and
    PairHasRationalSquaredDistance A D
    and
    PairHasRationalSquaredDistance B C
    and
    PairHasRationalSquaredDistance B D
    and
    PairHasRationalSquaredDistance C D

  proposition : Set
  proposition =
    (A B C D : Point R) ->
    GeneralPosition A B C D ->
    AllSquaredDistancesRational A B C D ->
    IsRational reals
      (divide reals
        (triangleArea reals A B C)
        (triangleArea reals A B D))

putnam-2018-a6 : Set1
putnam-2018-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam2018A6Statement.proposition reals
