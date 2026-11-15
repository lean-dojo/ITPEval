-- Statement-only formalization of "The Isoperimetric Theorem" from Hundred Theorems item 043.
-- It states the sharp area bound and equality case for rectifiable simple closed plane curves.
-- This file contains no proof.

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_

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
  zero<= : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

data _<N_ : Nat -> Nat -> Set where
  zero<suc : {n : Nat} -> zero <N suc n
  suc<suc : {m n : Nat} -> m <N n -> suc m <N suc n

record OrderedField (R : Set) : Set1 where
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
          (x : R) ->
          P x ->
          lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          Both
            ((x : R) -> P x -> lessOrEqual x supremum)
            ((upper : R) ->
              ((x : R) -> P x -> lessOrEqual x upper) ->
              lessOrEqual supremum upper))

open OrderedField

subtract :
  {R : Set} ->
  OrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  OrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

divide :
  {R : Set} ->
  OrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  OrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  Both (lessOrEqual reals x y) (x != y)

SequentialLimit :
  {R : Set} ->
  OrderedField R ->
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

oddNatural : Nat -> Nat
oddNatural zero = suc zero
oddNatural (suc n) = suc (suc (oddNatural n))

alternatingUnit :
  {R : Set} ->
  OrderedField R ->
  Nat ->
  R
alternatingUnit reals zero =
  oneR reals
alternatingUnit reals (suc n) =
  negate reals (alternatingUnit reals n)

leibnizTerm :
  {R : Set} ->
  OrderedField R ->
  Nat ->
  R
leibnizTerm reals n =
  multiply reals
    (alternatingUnit reals n)
    (inverse reals
      (fromNat reals (oddNatural n)))

leibnizPartialSum :
  {R : Set} ->
  OrderedField R ->
  Nat ->
  R
leibnizPartialSum reals zero =
  leibnizTerm reals zero
leibnizPartialSum reals (suc n) =
  add reals
    (leibnizPartialSum reals n)
    (leibnizTerm reals (suc n))

piApproximation :
  {R : Set} ->
  OrderedField R ->
  Nat ->
  R
piApproximation reals n =
  multiply reals
    (fromNat reals 4)
    (leibnizPartialSum reals n)

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Curve : Set -> Set
Curve R = R -> Point R

Region : Set -> Set1
Region R = Point R -> Set

UnitInterval :
  {R : Set} ->
  OrderedField R ->
  R ->
  Set
UnitInterval reals t =
  Both
    (lessOrEqual reals (zeroR reals) t)
    (lessOrEqual reals t (oneR reals))

Nonnegative :
  {R : Set} ->
  OrderedField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zeroR reals) x

pathImage :
  {R : Set} ->
  OrderedField R ->
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

squaredDistance :
  {R : Set} ->
  OrderedField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals
        (x-coordinate p)
        (x-coordinate q)))
    (square reals
      (subtract reals
        (y-coordinate p)
        (y-coordinate q)))

parameterSquaredDistance :
  {R : Set} ->
  OrderedField R ->
  R ->
  R ->
  R
parameterSquaredDistance reals x y =
  square reals (subtract reals x y)

record StandardRealPlane (R : Set) : Set1 where
  field
    algebra : OrderedField R
    pi : R
    squareRoot : R -> R

    square-root-nonnegative :
      (x : R) ->
      Nonnegative algebra (squareRoot x)
    square-root-square :
      (x : R) ->
      Nonnegative algebra x ->
      square algebra (squareRoot x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqual algebra x (zeroR algebra) ->
      squareRoot x == zeroR algebra

    pi-leibniz-limit :
      SequentialLimit algebra
        (piApproximation algebra)
        pi
    pi-lower-bound :
      StrictLess algebra
        (fromNat algebra 3)
        pi
    pi-upper-bound :
      StrictLess algebra
        pi
        (fromNat algebra 4)

open StandardRealPlane

module PlaneDefinitions
  {R : Set}
  (plane : StandardRealPlane R) where

  reals : OrderedField R
  reals = algebra plane

  origin : Point R
  origin = point (zeroR reals) (zeroR reals)

  PointNear : R -> Point R -> Point R -> Set
  PointNear epsilon p q =
    StrictLess reals
      (squaredDistance reals p q)
      (square reals epsilon)

  ParameterNear : R -> R -> R -> Set
  ParameterNear epsilon x y =
    StrictLess reals
      (parameterSquaredDistance reals x y)
      (square reals epsilon)

  ContinuousCurve : Curve R -> Set
  ContinuousCurve g =
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
            ParameterNear delta s t ->
            PointNear epsilon (g s) (g t)))

  Endpoints : R -> R -> Set
  Endpoints s t =
    Either
      (Both
        (s == zeroR reals)
        (t == oneR reals))
      (Both
        (s == oneR reals)
        (t == zeroR reals))

  SimplePath : Curve R -> Set
  SimplePath g =
    Both
      (ContinuousCurve g)
      ((s t : R) ->
        UnitInterval reals s ->
        UnitInterval reals t ->
        g s == g t ->
        Either (s == t) (Endpoints s t))

  record Partition : Set where
    constructor partition
    field
      count : Nat
      parameter : Nat -> R
      begins-at-zero :
        parameter zero == zeroR reals
      ends-at-one :
        parameter count == oneR reals
      increasing :
        (i : Nat) ->
        i <N count ->
        lessOrEqual reals
          (parameter i)
          (parameter (suc i))

  open Partition

  pointDistance : Point R -> Point R -> R
  pointDistance p q =
    squareRoot plane (squaredDistance reals p q)

  distanceSum :
    Curve R ->
    (Nat -> R) ->
    Nat ->
    R
  distanceSum g parameters zero =
    zeroR reals
  distanceSum g parameters (suc n) =
    add reals
      (distanceSum g parameters n)
      (pointDistance
        (g (parameters n))
        (g (parameters (suc n))))

  partitionLength : Curve R -> Partition -> R
  partitionLength g p =
    distanceSum g (parameter p) (count p)

  UpperLengthBound : Curve R -> R -> Set
  UpperLengthBound g bound =
    (p : Partition) ->
    lessOrEqual reals (partitionLength g p) bound

  PathLength : Curve R -> R -> Set
  PathLength g length =
    Both
      (UpperLengthBound g length)
      ((bound : R) ->
        UpperLengthBound g bound ->
        lessOrEqual reals length bound)

  RectifiablePath : Curve R -> Set
  RectifiablePath g =
    Both
      (ContinuousCurve g)
      (Exists R (\ length -> PathLength g length))

  PathConnectedOutside :
    Region R ->
    Point R ->
    Point R ->
    Set
  PathConnectedOutside region p q =
    Exists (Curve R)
      (\ h ->
        Both
          (ContinuousCurve h)
          (Both
            (Both
              (h (zeroR reals) == p)
              (h (oneR reals) == q))
            ((t : R) ->
              UnitInterval reals t ->
              Not (region (h t)))))

  Inside : Region R -> Region R
  Inside region p =
    Both
      (Not (region p))
      (Exists R
        (\ bound ->
          Both
            (Nonnegative reals bound)
            ((q : Point R) ->
              PathConnectedOutside region p q ->
              lessOrEqual reals
                (squaredDistance reals q origin)
                (square reals bound))))

  sphere : Point R -> R -> Region R
  sphere center radius p =
    Both
      (Nonnegative reals radius)
      (squaredDistance reals p center ==
        square reals radius)

  record Rectangle : Set where
    constructor rectangle
    field
      lower-x upper-x : R
      lower-y upper-y : R

  open Rectangle

  ValidRectangle : Rectangle -> Set
  ValidRectangle box =
    Both
      (lessOrEqual reals (lower-x box) (upper-x box))
      (lessOrEqual reals (lower-y box) (upper-y box))

  RectangleContains : Rectangle -> Point R -> Set
  RectangleContains box p =
    Both
      (Both
        (StrictLess reals (lower-x box) (x-coordinate p))
        (StrictLess reals (x-coordinate p) (upper-x box)))
      (Both
        (StrictLess reals (lower-y box) (y-coordinate p))
        (StrictLess reals (y-coordinate p) (upper-y box)))

  rectangleArea : Rectangle -> R
  rectangleArea box =
    multiply reals
      (subtract reals (upper-x box) (lower-x box))
      (subtract reals (upper-y box) (lower-y box))

  RectangleCover : Set
  RectangleCover = Nat -> Rectangle

  ValidCover : RectangleCover -> Set
  ValidCover cover =
    (n : Nat) -> ValidRectangle (cover n)

  Covers : RectangleCover -> Region R -> Set
  Covers cover region =
    (p : Point R) ->
    region p ->
    Exists Nat (\ n -> RectangleContains (cover n) p)

  coverPartialArea : RectangleCover -> Nat -> R
  coverPartialArea cover zero =
    rectangleArea (cover zero)
  coverPartialArea cover (suc n) =
    add reals
      (coverPartialArea cover n)
      (rectangleArea (cover (suc n)))

  CoverTotal : RectangleCover -> R -> Set
  CoverTotal cover total =
    SequentialLimit reals (coverPartialArea cover) total

  CoverCost : Region R -> R -> Set
  CoverCost region total =
    Exists RectangleCover
      (\ cover ->
        Both
          (ValidCover cover)
          (Both
            (Covers cover region)
            (CoverTotal cover total)))

  LowerBound : (R -> Set) -> R -> Set
  LowerBound values bound =
    (value : R) ->
    values value ->
    lessOrEqual reals bound value

  GreatestLowerBound : (R -> Set) -> R -> Set
  GreatestLowerBound values infimum =
    Both
      (LowerBound values infimum)
      ((bound : R) ->
        LowerBound values bound ->
        lessOrEqual reals bound infimum)

  PlanarLebesgueArea : Region R -> R -> Set
  PlanarLebesgueArea region area =
    GreatestLowerBound (CoverCost region) area

  FourPiTimes : R -> R
  FourPiTimes area =
    multiply reals
      (multiply reals (fromNat reals 4) (pi plane))
      area

  proposition : Set
  proposition =
    (L : R) ->
    (g : Curve R) ->
    RectifiablePath g ->
    SimplePath g ->
    g (oneR reals) == g (zeroR reals) ->
    PathLength g L ->
    Exists R
      (\ area ->
        Both
          (PlanarLebesgueArea
            (Inside (pathImage reals g))
            area)
          (Both
            (lessOrEqual reals
              (FourPiTimes area)
              (square reals L))
            (FourPiTimes area == square reals L ->
              Exists (Point R)
                (\ center ->
                  Exists R
                    (\ radius ->
                      RegionEquivalent
                        (pathImage reals g)
                        (sphere center radius))))))

the-isoperimetric-theorem : Set1
the-isoperimetric-theorem =
  (R : Set) ->
  (plane : StandardRealPlane R) ->
  PlaneDefinitions.proposition plane
