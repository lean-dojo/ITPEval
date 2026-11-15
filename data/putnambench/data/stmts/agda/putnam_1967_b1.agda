-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_b1:
-- a cyclic hexagon with three alternating sides equal to the circle radius has
-- an equilateral triangle formed by the other three side midpoints. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
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

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiply reals x x

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  add reals (oneR reals) (oneR reals)

half :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
half reals =
  inverse reals (two reals)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Nonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zeroR reals) x

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

affinePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R ->
  Point R
affinePoint reals t p q =
  point
    (add reals
      (multiply reals
        (subtract reals (oneR reals) t)
        (x-coordinate p))
      (multiply reals t (x-coordinate q)))
    (add reals
      (multiply reals
        (subtract reals (oneR reals) t)
        (y-coordinate p))
      (multiply reals t (y-coordinate q)))

midpoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
midpoint reals p q =
  affinePoint reals (half reals) p q

data Fin6 : Set where
  i0 i1 i2 i3 i4 i5 : Fin6

next6 : Fin6 -> Fin6
next6 i0 = i1
next6 i1 = i2
next6 i2 = i3
next6 i3 = i4
next6 i4 = i5
next6 i5 = i0

sum6 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin6 -> R) ->
  R
sum6 reals values =
  add reals (values i0)
    (add reals (values i1)
      (add reals (values i2)
        (add reals (values i3)
          (add reals (values i4) (values i5)))))

weightedPoint6 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin6 -> R) ->
  (Fin6 -> Point R) ->
  Point R
weightedPoint6 reals weights vertices =
  point
    (sum6 reals
      (\ i ->
        multiply reals
          (weights i)
          (x-coordinate (vertices i))))
    (sum6 reals
      (\ i ->
        multiply reals
          (weights i)
          (y-coordinate (vertices i))))

ConvexHull6 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin6 -> Point R) ->
  Point R ->
  Set
ConvexHull6 {R} reals vertices p =
  Exists (Fin6 -> R)
    (\ weights ->
      ((i : Fin6) -> Nonnegative reals (weights i))
      and
      sum6 reals weights == oneR reals
      and
      p == weightedPoint6 reals weights vertices)

ClosedSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
ClosedSegment {R} reals p q x =
  Exists R
    (\ t ->
      lessOrEqual reals (zeroR reals) t
      and
      lessOrEqual reals t (oneR reals)
      and
      x == affinePoint reals t p q)

InteriorOfConvexHull6 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin6 -> Point R) ->
  Point R ->
  Set
InteriorOfConvexHull6 {R} reals vertices p =
  Exists R
    (\ epsilon ->
      StrictLess reals (zeroR reals) epsilon
      and
      ((q : Point R) ->
        StrictLess reals (distance reals p q) epsilon ->
        ConvexHull6 reals vertices q))

SegmentMeetsInterior :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin6 -> Point R) ->
  Fin6 ->
  Fin6 ->
  Set
SegmentMeetsInterior {R} reals vertices i j =
  Exists (Point R)
    (\ x ->
      ClosedSegment reals (vertices i) (vertices j) x
      and
      InteriorOfConvexHull6 reals vertices x)

CyclicOrder :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin6 -> Point R) ->
  Set
CyclicOrder reals vertices =
  (i j : Fin6) ->
  i != j ->
  next6 i == j
  or
  i == next6 j
  or
  SegmentMeetsInterior reals vertices i j

module Putnam1967B1Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (r : R) ->
    (L : Fin6 -> Point R) ->
    (P Q T : Point R) ->
    P == midpoint reals (L i1) (L i2) ->
    Q == midpoint reals (L i3) (L i4) ->
    T == midpoint reals (L i5) (L i0) ->
    StrictLess reals (zeroR reals) r ->
    Exists (Point R)
      (\ center ->
        (i : Fin6) ->
        distance reals center (L i) == r) ->
    CyclicOrder reals L ->
    (distance reals (L i0) (L i1) == r
      and
      distance reals (L i2) (L i3) == r
      and
      distance reals (L i4) (L i5) == r) ->
    (L i1 != L i2
      and
      L i3 != L i4
      and
      L i5 != L i0) ->
    distance reals P Q == distance reals T P
    and
    distance reals Q T == distance reals P Q

putnam-1967-b1 : Set1
putnam-1967-b1 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1967B1Statement.proposition reals
