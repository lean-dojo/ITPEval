-- Statement-only formalization of Hundred Theorems artifact
-- hundred-theorems__agda__092, "Pick's Theorem": the area of a simple closed
-- lattice polygon is its number of interior lattice points plus half its
-- number of boundary lattice points minus one. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A -> Either A B
  right : B -> Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

data All {A : Set} (P : A -> Set) : List A -> Set where
  all[] : All P []
  all∷  : {x : A} {xs : List A} -> P x -> All P xs -> All P (x ∷ xs)

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
      Either (lessOrEqual x y) (lessOrEqual y x)
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
      Both (lessOrEqual zeroR oneR) (zeroR != oneR)

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
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

fromInt :
  {R : Set} ->
  CompleteOrderedField R ->
  Int ->
  R
fromInt reals (pos n) =
  fromNat reals n
fromInt reals (negsuc n) =
  negate reals (fromNat reals (suc n))

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Region : Set -> Set1
Region R = Point R -> Set

Curve : Set -> Set
Curve R = R -> Point R

UnitInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
UnitInterval reals t =
  Both
    (lessOrEqual reals (zeroR reals) t)
    (lessOrEqual reals t (oneR reals))

Nonnegative :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zeroR reals) x

addPoint :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R
addPoint reals p q =
  point
    (add reals (x-coordinate p) (x-coordinate q))
    (add reals (y-coordinate p) (y-coordinate q))

scalePoint :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Point R ->
  Point R
scalePoint reals scalar p =
  point
    (multiply reals scalar (x-coordinate p))
    (multiply reals scalar (y-coordinate p))

affinePoint :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R ->
  Point R
affinePoint reals p q t =
  addPoint reals
    (scalePoint reals (subtract reals (oneR reals) t) p)
    (scalePoint reals t q)

Segment :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Segment {R} reals p q x =
  Exists R
    (\ t ->
      Both
        (UnitInterval reals t)
        (affinePoint reals p q t == x))

BoundaryFrom :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  List (Point R) ->
  Region R
BoundaryFrom reals firstPoint previous [] x =
  Segment reals previous firstPoint x
BoundaryFrom reals firstPoint previous (next ∷ rest) x =
  Either
    (Segment reals previous next x)
    (BoundaryFrom reals firstPoint next rest x)

polygonBoundary :
  {R : Set} ->
  CompleteOrderedField R ->
  List (Point R) ->
  Region R
polygonBoundary reals [] _ =
  Bottom
polygonBoundary reals (firstPoint ∷ rest) =
  BoundaryFrom reals firstPoint firstPoint rest

IntegerCoordinate :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
IntegerCoordinate reals x =
  Exists Int (\ z -> x == fromInt reals z)

IntegerPoint :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Set
IntegerPoint reals p =
  Both
    (IntegerCoordinate reals (x-coordinate p))
    (IntegerCoordinate reals (y-coordinate p))

squaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

parameterSquaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
parameterSquaredDistance reals s t =
  square reals (subtract reals s t)

PointNear :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Point R ->
  Point R ->
  Set
PointNear reals epsilon p q =
  StrictLess reals
    (squaredDistance reals p q)
    (square reals epsilon)

ParameterNear :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R ->
  Set
ParameterNear reals epsilon s t =
  StrictLess reals
    (parameterSquaredDistance reals s t)
    (square reals epsilon)

ContinuousCurve :
  {R : Set} ->
  CompleteOrderedField R ->
  Curve R ->
  Set
ContinuousCurve {R} reals g =
  (t : R) ->
  UnitInterval reals t ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      Both
        (StrictLess reals (zeroR reals) delta)
        ((s : R) ->
          UnitInterval reals s ->
          ParameterNear reals delta s t ->
          PointNear reals epsilon (g s) (g t)))

Endpoints :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
Endpoints reals s t =
  Either
    (Both (s == zeroR reals) (t == oneR reals))
    (Both (s == oneR reals) (t == zeroR reals))

SimplePath :
  {R : Set} ->
  CompleteOrderedField R ->
  Curve R ->
  Set
SimplePath {R} reals g =
  Both
    (ContinuousCurve reals g)
    ((s t : R) ->
      UnitInterval reals s ->
      UnitInterval reals t ->
      g s == g t ->
      Either (s == t) (Endpoints reals s t))

pathImage :
  {R : Set} ->
  CompleteOrderedField R ->
  Curve R ->
  Region R
pathImage {R} reals g p =
  Exists R
    (\ t ->
      Both
        (UnitInterval reals t)
        (g t == p))

RegionEquivalent :
  {R : Set} ->
  Region R ->
  Region R ->
  Set
RegionEquivalent {R} leftRegion rightRegion =
  (p : Point R) ->
  Iff (leftRegion p) (rightRegion p)

SimpleClosedPolygon :
  {R : Set} ->
  CompleteOrderedField R ->
  List (Point R) ->
  Set
SimpleClosedPolygon reals vertices =
  Exists (Curve _)
    (\ g ->
      Both
        (SimplePath reals g)
        (Both
          (g (zeroR reals) == g (oneR reals))
          (RegionEquivalent
            (pathImage reals g)
            (polygonBoundary reals vertices))))

origin :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R
origin reals =
  point (zeroR reals) (zeroR reals)

PathConnectedOutside :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  Point R ->
  Point R ->
  Set
PathConnectedOutside {R} reals region p q =
  Exists (Curve R)
    (\ h ->
      Both
        (ContinuousCurve reals h)
        (Both
          (Both
            (h (zeroR reals) == p)
            (h (oneR reals) == q))
          ((t : R) ->
            UnitInterval reals t ->
            Not (region (h t)))))

Inside :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  Region R
Inside {R} reals region p =
  Both
    (Not (region p))
    (Exists R
      (\ bound ->
        Both
          (Nonnegative reals bound)
          ((q : Point R) ->
            PathConnectedOutside reals region p q ->
            lessOrEqual reals
              (squaredDistance reals q (origin reals))
              (square reals bound))))

data HasCardinality
  {R : Set}
  (P : Point R -> Set)
  (cardinality : Nat) : Set where
  cardinality-witness :
    (enumerate : Fin cardinality -> Point R) ->
    ((i : Fin cardinality) -> P (enumerate i)) ->
    ((p : Point R) ->
      P p ->
      Exists (Fin cardinality) (\ i -> p == enumerate i)) ->
    ((i j : Fin cardinality) ->
      enumerate i == enumerate j ->
      i == j) ->
    HasCardinality P cardinality

data Rectangle {R : Set} : Set where
  rectangle : R -> R -> R -> R -> Rectangle

lower-x :
  {R : Set} ->
  Rectangle {R} ->
  R
lower-x (rectangle lx ux ly uy) = lx

upper-x :
  {R : Set} ->
  Rectangle {R} ->
  R
upper-x (rectangle lx ux ly uy) = ux

lower-y :
  {R : Set} ->
  Rectangle {R} ->
  R
lower-y (rectangle lx ux ly uy) = ly

upper-y :
  {R : Set} ->
  Rectangle {R} ->
  R
upper-y (rectangle lx ux ly uy) = uy

ValidRectangle :
  {R : Set} ->
  CompleteOrderedField R ->
  Rectangle {R} ->
  Set
ValidRectangle reals box =
  Both
    (lessOrEqual reals (lower-x box) (upper-x box))
    (lessOrEqual reals (lower-y box) (upper-y box))

RectangleContains :
  {R : Set} ->
  CompleteOrderedField R ->
  Rectangle {R} ->
  Point R ->
  Set
RectangleContains reals box p =
  Both
    (Both
      (StrictLess reals (lower-x box) (x-coordinate p))
      (StrictLess reals (x-coordinate p) (upper-x box)))
    (Both
      (StrictLess reals (lower-y box) (y-coordinate p))
      (StrictLess reals (y-coordinate p) (upper-y box)))

rectangleArea :
  {R : Set} ->
  CompleteOrderedField R ->
  Rectangle {R} ->
  R
rectangleArea reals box =
  multiply reals
    (subtract reals (upper-x box) (lower-x box))
    (subtract reals (upper-y box) (lower-y box))

SequentialLimit :
  {R : Set} ->
  CompleteOrderedField R ->
  (Nat -> R) ->
  R ->
  Set
SequentialLimit {R} reals sequence limit =
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists Nat
    (\ cutoff ->
      (n : Nat) ->
      cutoff <=N n ->
      Both
        (StrictLess reals
          (subtract reals limit epsilon)
          (sequence n))
        (StrictLess reals
          (sequence n)
          (add reals limit epsilon)))

RectangleCover :
  {R : Set} ->
  Set
RectangleCover {R} =
  Nat -> Rectangle {R}

ValidCover :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover {R} ->
  Set
ValidCover reals cover =
  (n : Nat) -> ValidRectangle reals (cover n)

Covers :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover {R} ->
  Region R ->
  Set
Covers {R} reals cover region =
  (p : Point R) ->
  region p ->
  Exists Nat (\ n -> RectangleContains reals (cover n) p)

coverPartialArea :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover {R} ->
  Nat ->
  R
coverPartialArea reals cover zero =
  rectangleArea reals (cover zero)
coverPartialArea reals cover (suc n) =
  add reals
    (coverPartialArea reals cover n)
    (rectangleArea reals (cover (suc n)))

CoverTotal :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover {R} ->
  R ->
  Set
CoverTotal reals cover total =
  SequentialLimit reals (coverPartialArea reals cover) total

CoverCost :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  R ->
  Set
CoverCost {R} reals region total =
  Exists (RectangleCover {R})
    (\ cover ->
      Both
        (ValidCover reals cover)
        (Both
          (Covers reals cover region)
          (CoverTotal reals cover total)))

LowerBound :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> Set) ->
  R ->
  Set
LowerBound {R} reals values bound =
  (value : R) ->
  values value ->
  lessOrEqual reals bound value

GreatestLowerBound :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> Set) ->
  R ->
  Set
GreatestLowerBound {R} reals values infimum =
  Both
    (LowerBound reals values infimum)
    ((bound : R) ->
      LowerBound reals values bound ->
      lessOrEqual reals bound infimum)

PlanarLebesgueArea :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  R ->
  Set
PlanarLebesgueArea reals region area =
  GreatestLowerBound reals (CoverCost reals region) area

module PickStatement
  {R : Set}
  (reals : CompleteOrderedField R) where

  boundaryLatticePoints :
    List (Point R) ->
    Point R ->
    Set
  boundaryLatticePoints vertices p =
    Both
      (polygonBoundary reals vertices p)
      (IntegerPoint reals p)

  interiorLatticePoints :
    List (Point R) ->
    Point R ->
    Set
  interiorLatticePoints vertices p =
    Both
      (Inside reals (polygonBoundary reals vertices) p)
      (IntegerPoint reals p)

  pickFormula :
    Nat ->
    Nat ->
    R
  pickFormula interiorCount boundaryCount =
    subtract reals
      (add reals
        (fromNat reals interiorCount)
        (divide reals
          (fromNat reals boundaryCount)
          (fromNat reals (suc (suc zero)))))
      (oneR reals)

  proposition : Set
  proposition =
    (vertices : List (Point R)) ->
    All (IntegerPoint reals) vertices ->
    SimpleClosedPolygon reals vertices ->
    (interiorCount boundaryCount : Nat) ->
    HasCardinality
      (interiorLatticePoints vertices)
      interiorCount ->
    HasCardinality
      (boundaryLatticePoints vertices)
      boundaryCount ->
    Exists R
      (\ area ->
        Both
          (PlanarLebesgueArea reals
            (Inside reals (polygonBoundary reals vertices))
            area)
          (area == pickFormula interiorCount boundaryCount))

pick-s-theorem : Set1
pick-s-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  PickStatement.proposition reals
