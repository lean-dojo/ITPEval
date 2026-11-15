-- Statement-only formalization of PutnamBench corpus artifact putnam_1965_a1:
-- a nondegenerate real-plane triangle with the stated external angle-bisector
-- and equal-distance conditions has angle CAB equal to pi / 15.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

oneN : Nat
oneN = suc zero

twoN : Nat
twoN = suc oneN

fourN : Nat
fourN = twoN + twoN

fifteenN : Nat
fifteenN =
  suc
    (suc
      (suc
        (suc
          (suc
            (suc
              (suc
                (suc
                  (suc
                    (suc
                      (suc
                        (suc
                          (suc
                            (suc
                              (suc zero))))))))))))))

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
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zeroR == x
    add-inverse :
      (x : R) -> add x (negate x) == zeroR

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
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
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) ->
      fromNat (m + n) == add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) ->
      fromNat (m * n) == multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n

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
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
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

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals (subtract reals center radius) x
  and
  StrictLess reals x (add reals center radius)

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals (naturalPower reals x n) x

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero term =
  zeroR reals
sumFirst reals (suc n) term =
  add reals
    (sumFirst reals n term)
    (term n)

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo reals sequence limit =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      CloseTo reals limit epsilon (sequence n))

SeriesHasSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
SeriesHasSum reals terms limit =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    limit

alternatingPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
alternatingPower reals n =
  naturalPower reals (negate reals (oneR reals)) n

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  divide reals
    (multiply reals
      (alternatingPower reals n)
      (naturalPower reals x (twoN * n)))
    (fromNat reals (factorial (twoN * n)))

leibnizTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R
leibnizTerm reals n =
  divide reals
    (alternatingPower reals n)
    (fromNat reals (suc (twoN * n)))

CosineValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
CosineValue reals x value =
  SeriesHasSum reals (cosineTerm reals x) value

record PiValue
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (value : R) : Set where
  field
    positive :
      StrictLess reals (zeroR reals) value
    leibniz-series :
      SeriesHasSum reals
        (leibnizTerm reals)
        (divide reals value (fromNat reals fourN))

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

record Vector (R : Set) : Set where
  constructor vector
  field
    x-component : R
    y-component : R

open Point
open Vector

zeroVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R
zeroVector reals =
  vector (zeroR reals) (zeroR reals)

ZeroVector :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R ->
  Set
ZeroVector reals v =
  x-component v == zeroR reals
  and
  y-component v == zeroR reals

vectorBetween :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Vector R
vectorBetween reals endpoint origin =
  vector
    (subtract reals
      (x-coordinate endpoint)
      (x-coordinate origin))
    (subtract reals
      (y-coordinate endpoint)
      (y-coordinate origin))

dot :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R ->
  Vector R ->
  R
dot reals u v =
  add reals
    (multiply reals (x-component u) (x-component v))
    (multiply reals (y-component u) (y-component v))

squaredNorm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R ->
  R
squaredNorm reals v =
  dot reals v v

norm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Vector R ->
  R
norm reals v =
  squareRoot reals (squaredNorm reals v)

ValidCosineInput :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
ValidCosineInput reals x =
  lessOrEqual reals (negate reals (oneR reals)) x
  and
  lessOrEqual reals x (oneR reals)

record StandardPlaneAngleGeometry
  {R : Set}
  (reals : CompleteOrderedRealField R) : Set1 where
  field
    cosine arccos : R -> R
    pi : R
    vectorAngle : Vector R -> Vector R -> R

    cosine-value :
      (x : R) ->
      CosineValue reals x (cosine x)
    pi-value :
      PiValue reals pi

    arccos-range :
      (x : R) ->
      ValidCosineInput reals x ->
      lessOrEqual reals (zeroR reals) (arccos x)
      and
      lessOrEqual reals (arccos x) pi
    cosine-arccos :
      (x : R) ->
      ValidCosineInput reals x ->
      cosine (arccos x) == x
    cosine-injective-on-angle-range :
      (x y : R) ->
      lessOrEqual reals (zeroR reals) x ->
      lessOrEqual reals x pi ->
      lessOrEqual reals (zeroR reals) y ->
      lessOrEqual reals y pi ->
      cosine x == cosine y ->
      x == y

    vector-angle-zero-left :
      (u v : Vector R) ->
      ZeroVector reals u ->
      vectorAngle u v ==
      divide reals pi (fromNat reals twoN)
    vector-angle-zero-right :
      (u v : Vector R) ->
      ZeroVector reals v ->
      vectorAngle u v ==
      divide reals pi (fromNat reals twoN)
    vector-angle-nonzero :
      (u v : Vector R) ->
      Not (ZeroVector reals u) ->
      Not (ZeroVector reals v) ->
      vectorAngle u v ==
      arccos
        (divide reals
          (dot reals u v)
          (multiply reals (norm reals u) (norm reals v)))

open StandardPlaneAngleGeometry

halfPi :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardPlaneAngleGeometry reals ->
  R
halfPi {reals = reals} geometry =
  divide reals
    (pi geometry)
    (fromNat reals twoN)

angleAt :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardPlaneAngleGeometry reals ->
  Point R ->
  Point R ->
  Point R ->
  R
angleAt {reals = reals} geometry a b c =
  vectorAngle geometry
    (vectorBetween reals a b)
    (vectorBetween reals c b)

distance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  norm reals (vectorBetween reals p q)

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
      (subtract reals (x-coordinate a) (x-coordinate b))
      (subtract reals (y-coordinate c) (y-coordinate b)))
    (multiply reals
      (subtract reals (y-coordinate a) (y-coordinate b))
      (subtract reals (x-coordinate c) (x-coordinate b)))

Collinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Collinear reals a b c =
  doubleSignedArea reals a b c == zeroR reals

putnam-1965-a1-solution :
  {R : Set} ->
  {reals : CompleteOrderedRealField R} ->
  StandardPlaneAngleGeometry reals ->
  R
putnam-1965-a1-solution {reals = reals} geometry =
  divide reals
    (pi geometry)
    (fromNat reals fifteenN)

module Putnam1965A1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (geometry : StandardPlaneAngleGeometry reals) where

  proposition : Set
  proposition =
    (A B C X Y : Point R) ->
    Not (Collinear reals A B C) ->
    (StrictLess reals
      (angleAt geometry C A B)
      (angleAt geometry B C A)
    and
    StrictLess reals
      (angleAt geometry B C A)
      (halfPi geometry)
    and
    StrictLess reals
      (halfPi geometry)
      (angleAt geometry A B C)) ->
    (Collinear reals X B C
    and
    angleAt geometry X A B ==
      divide reals
        (subtract reals
          (pi geometry)
          (angleAt geometry C A B))
        (fromNat reals twoN)
    and
    distance reals A X == distance reals A B) ->
    (Collinear reals Y C A
    and
    angleAt geometry Y B C ==
      divide reals
        (subtract reals
          (pi geometry)
          (angleAt geometry A B C))
        (fromNat reals twoN)
    and
    distance reals B Y == distance reals A B) ->
    angleAt geometry C A B ==
    putnam-1965-a1-solution geometry

putnam-1965-a1 : Set1
putnam-1965-a1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (geometry : StandardPlaneAngleGeometry reals) ->
  Putnam1965A1Statement.proposition reals geometry
