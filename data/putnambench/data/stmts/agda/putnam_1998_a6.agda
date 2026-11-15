-- Statement-only formalization of PutnamBench corpus artifact putnam_1998_a6
-- (putnambench__agda__putnam_1998_a6): distinct lattice points in the real
-- plane satisfying the stated length-area inequality form three vertices of
-- a square. This file contains no proof.

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

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    add multiply : R -> R -> R
    negate inverse squareRoot : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Nat -> R
    supremum infimum : (R -> Set) -> R

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

    supremum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      ((x : R) ->
        P x ->
        lessOrEqual x (supremum P))
      and
      ((upper : R) ->
        ((x : R) ->
          P x ->
          lessOrEqual x upper) ->
        lessOrEqual (supremum P) upper)

    infimum-property :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ lower ->
          (x : R) ->
          P x ->
          lessOrEqual lower x) ->
      ((x : R) ->
        P x ->
        lessOrEqual (infimum P) x)
      and
      ((lower : R) ->
        ((x : R) ->
          P x ->
          lessOrEqual lower x) ->
        lessOrEqual lower (infimum P))

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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

eightN : Nat
eightN =
  suc (suc (suc (suc (suc (suc (suc oneN))))))

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

distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  squareRoot reals (squaredDistance reals p q)

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

dotAt :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
dotAt reals q p r =
  add reals
    (multiply reals
      (subtract reals (x-coordinate p) (x-coordinate q))
      (subtract reals (x-coordinate r) (x-coordinate q)))
    (multiply reals
      (subtract reals (y-coordinate p) (y-coordinate q))
      (subtract reals (y-coordinate r) (y-coordinate q)))

module Putnam1998A6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  IntegerCoordinates :
    Point R ->
    Point R ->
    Point R ->
    Set
  IntegerCoordinates A B C =
    Exists Int
      (\ a ->
        Exists Int
          (\ b ->
            Exists Int
              (\ c ->
                x-coordinate A == fromInt reals a
                and
                x-coordinate B == fromInt reals b
                and
                x-coordinate C == fromInt reals c)))
    and
    Exists Int
      (\ a ->
        Exists Int
          (\ b ->
            Exists Int
              (\ c ->
                y-coordinate A == fromInt reals a
                and
                y-coordinate B == fromInt reals b
                and
                y-coordinate C == fromInt reals c)))

  Distinct :
    Point R ->
    Point R ->
    Point R ->
    Set
  Distinct A B C =
    A != B and A != C and B != C

  AreaBound :
    Point R ->
    Point R ->
    Point R ->
    Set
  AreaBound A B C =
    StrictLess reals
      (square reals
        (add reals
          (distance reals A B)
          (distance reals B C)))
      (add reals
        (multiply reals
          (fromNat reals eightN)
          (triangleArea reals A B C))
        (oneR reals))

  ThreeSquare :
    Point R ->
    Point R ->
    Point R ->
    Set
  ThreeSquare P Q R' =
    distance reals Q P == distance reals Q R'
    and
    dotAt reals Q P R' == zeroR reals

  proposition : Set
  proposition =
    (A B C : Point R) ->
    IntegerCoordinates A B C ->
    Distinct A B C ->
    AreaBound A B C ->
    ThreeSquare A B C
    or
    ThreeSquare B C A
    or
    ThreeSquare C A B

putnam-1998-a6 : Set1
putnam-1998-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1998A6Statement.proposition reals
