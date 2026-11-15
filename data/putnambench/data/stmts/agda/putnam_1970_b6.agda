-- Statement-only formalization of PutnamBench corpus artifact putnam_1970_b6:
-- an ordered nondegenerate quadrilateral tangent to an interior circle and
-- having area equal to the square root of the product of its side lengths is
-- cyclic. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
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

record Iff (A B : Set) : Set where
  constructor iff
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record ExistsUnique (A : Set) (P : A -> Set) : Set where
  constructor unique-witness
  field
    value      : A
    property   : P value
    uniqueness : (other : A) -> P other -> other == value

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

PointEqual :
  {R : Set} ->
  Point R ->
  Point R ->
  Set
PointEqual p q =
  x-coordinate p == x-coordinate q
  and
  y-coordinate p == y-coordinate q

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

determinant :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
determinant reals a b c =
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
  determinant reals a b c == zeroR reals

Predicate : Set -> Set1
Predicate A =
  A -> Set

SameSet :
  {A : Set} ->
  Predicate A ->
  Predicate A ->
  Set
SameSet {A} S T =
  (x : A) -> Iff (S x) (T x)

data Fin4 : Set where
  i0 i1 i2 i3 : Fin4

next4 : Fin4 -> Fin4
next4 i0 = i1
next4 i1 = i2
next4 i2 = i3
next4 i3 = i0

sum4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> R) ->
  R
sum4 reals values =
  add reals
    (add reals (values i0) (values i1))
    (add reals (values i2) (values i3))

weightedPoint4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> R) ->
  (Fin4 -> Point R) ->
  Point R
weightedPoint4 reals weights vertices =
  point
    (sum4 reals
      (\ i ->
        multiply reals
          (weights i)
          (x-coordinate (vertices i))))
    (sum4 reals
      (\ i ->
        multiply reals
          (weights i)
          (y-coordinate (vertices i))))

VertexSet :
  {R : Set} ->
  (Fin4 -> Point R) ->
  Predicate (Point R)
VertexSet vertices p =
  Exists Fin4 (\ i -> p == vertices i)

PairwiseDistinct :
  {R : Set} ->
  (Fin4 -> Point R) ->
  Set
PairwiseDistinct vertices =
  (i j : Fin4) ->
  i != j ->
  vertices i != vertices j

NoThreeCollinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate (Point R) ->
  Set
NoThreeCollinear {R} reals S =
  (a b c : Point R) ->
  S a ->
  S b ->
  S c ->
  a != b ->
  b != c ->
  c != a ->
  Not (Collinear reals a b c)

ExactlyFourNoncollinear :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate (Point R) ->
  Set
ExactlyFourNoncollinear {R} reals S =
  Exists (Fin4 -> Point R)
    (\ vertices ->
      PairwiseDistinct vertices
      and
      SameSet S (VertexSet vertices))
  and
  NoThreeCollinear reals S

ConvexHull4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  Point R ->
  Set
ConvexHull4 {R} reals vertices p =
  Exists (Fin4 -> R)
    (\ weights ->
      ((i : Fin4) -> Nonnegative reals (weights i))
      and
      sum4 reals weights == oneR reals
      and
      PointEqual p (weightedPoint4 reals weights vertices))

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
      PointEqual x (affinePoint reals t p q))

InteriorOfConvexHull4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  Point R ->
  Set
InteriorOfConvexHull4 {R} reals vertices p =
  Exists R
    (\ epsilon ->
      StrictLess reals (zeroR reals) epsilon
      and
      ((q : Point R) ->
        StrictLess reals (distance reals p q) epsilon ->
        ConvexHull4 reals vertices q))

EdgesAvoidInterior :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  Set
EdgesAvoidInterior {R} reals vertices =
  (i : Fin4) ->
  (p : Point R) ->
  ClosedSegment reals (vertices i) (vertices (next4 i)) p ->
  Not (InteriorOfConvexHull4 reals vertices p)

CircumscribedAboutCircle :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  Set
CircumscribedAboutCircle {R} reals vertices =
  Exists (Point R)
    (\ center ->
      Exists R
        (\ radius ->
          ConvexHull4 reals vertices center
          and
          StrictLess reals (zeroR reals) radius
          and
          ((i : Fin4) ->
            ExistsUnique (Point R)
              (\ contact ->
                Collinear reals
                  contact
                  (vertices i)
                  (vertices (next4 i))
                and
                distance reals center contact == radius))))

cross :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
cross reals p q =
  subtract reals
    (multiply reals (x-coordinate p) (y-coordinate q))
    (multiply reals (y-coordinate p) (x-coordinate q))

signedDoubleArea4 :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  R
signedDoubleArea4 reals vertices =
  add reals
    (add reals
      (cross reals (vertices i0) (vertices i1))
      (cross reals (vertices i1) (vertices i2)))
    (add reals
      (cross reals (vertices i2) (vertices i3))
      (cross reals (vertices i3) (vertices i0)))

convexQuadrilateralArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  R
convexQuadrilateralArea reals vertices =
  multiply reals
    (half reals)
    (squareRoot reals
      (square reals (signedDoubleArea4 reals vertices)))

sideLengthProduct :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  R
sideLengthProduct reals vertices =
  multiply reals
    (multiply reals
      (multiply reals
        (distance reals (vertices i0) (vertices i1))
        (distance reals (vertices i1) (vertices i2)))
      (distance reals (vertices i2) (vertices i3)))
    (distance reals (vertices i3) (vertices i0))

PositiveSideLengths :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Fin4 -> Point R) ->
  Set
PositiveSideLengths reals vertices =
  StrictLess reals
    (zeroR reals)
    (distance reals (vertices i0) (vertices i1))
  and
  StrictLess reals
    (zeroR reals)
    (distance reals (vertices i1) (vertices i2))
  and
  StrictLess reals
    (zeroR reals)
    (distance reals (vertices i2) (vertices i3))
  and
  StrictLess reals
    (zeroR reals)
    (distance reals (vertices i3) (vertices i0))

Cospherical :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate (Point R) ->
  Set
Cospherical {R} reals S =
  Exists (Point R)
    (\ center ->
      Exists R
        (\ radius ->
          (p : Point R) ->
          S p ->
          distance reals p center == radius))

module Putnam1970B6Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set1
  proposition =
    (vertices : Fin4 -> Point R) ->
    (S : Predicate (Point R)) ->
    SameSet S (VertexSet vertices) ->
    ExactlyFourNoncollinear reals S ->
    PositiveSideLengths reals vertices ->
    EdgesAvoidInterior reals vertices ->
    CircumscribedAboutCircle reals vertices ->
    convexQuadrilateralArea reals vertices
      ==
    squareRoot reals (sideLengthProduct reals vertices) ->
    Cospherical reals S

putnam-1970-b6 : Set1
putnam-1970-b6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1970B6Statement.proposition reals
