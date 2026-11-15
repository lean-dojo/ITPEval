-- Statement-only formalization of PutnamBench corpus artifact putnam_2024_a5
-- (putnambench__agda__putnam_2024_a5): for random endpoints on the circle of
-- radius 9, the disk-center parameter in [0,8] minimizing the probability
-- that the chord meets the unit disk is exactly r = 0. This file contains no proof.

{-# OPTIONS --safe #-}

module Main where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

Predicate : Set -> Set1
Predicate A =
  A -> Set

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

oneN : Nat
oneN =
  suc zero

twoN : Nat
twoN =
  suc oneN

eightN : Nat
eightN =
  twoN * twoN * twoN

nineN : Nat
nineN =
  suc eightN

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

InClosedInterval :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
InClosedInterval reals lower upper x =
  lessOrEqual reals lower x
  and
  lessOrEqual reals x upper

CloseTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Set
CloseTo reals center radius x =
  StrictLess reals
    (subtract reals center radius)
    x
  and
  StrictLess reals
    x
    (add reals center radius)

sumFirst :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> R) ->
  R
sumFirst reals zero terms =
  zeroR reals
sumFirst reals (suc n) terms =
  add reals
    (sumFirst reals n terms)
    (terms n)

factorial : Nat -> Nat
factorial zero =
  oneN
factorial (suc n) =
  suc n * factorial n

naturalPower :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
naturalPower reals x zero =
  oneR reals
naturalPower reals x (suc n) =
  multiply reals
    (naturalPower reals x n)
    x

alternate :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  R ->
  R
alternate reals zero x =
  x
alternate reals (suc n) x =
  negate reals (alternate reals n x)

evenExponent : Nat -> Nat
evenExponent n =
  n + n

oddExponent : Nat -> Nat
oddExponent n =
  suc (evenExponent n)

sineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
sineTerm reals x n =
  alternate reals n
    (divide reals
      (naturalPower reals x (oddExponent n))
      (fromNat reals (factorial (oddExponent n))))

cosineTerm :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Nat ->
  R
cosineTerm reals x n =
  alternate reals n
    (divide reals
      (naturalPower reals x (evenExponent n))
      (fromNat reals (factorial (evenExponent n))))

ConvergesTo :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  R ->
  Set
ConvergesTo {R} reals sequence limit =
  (epsilon : R) ->
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
SeriesHasSum reals terms value =
  ConvergesTo reals
    (\ n -> sumFirst reals n terms)
    value

record StandardTrigonometry
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    sine cosine : R -> R
    pi : R

    sine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (sineTerm reals x)
        (sine x)
    cosine-is-power-series :
      (x : R) ->
      SeriesHasSum reals
        (cosineTerm reals x)
        (cosine x)

    pi-positive :
      StrictLess reals (zeroR reals) pi
    sine-pi-zero :
      sine pi == zeroR reals
    pi-is-first-positive-sine-zero :
      (x : R) ->
      StrictLess reals (zeroR reals) x ->
      sine x == zeroR reals ->
      lessOrEqual reals pi x

open StandardTrigonometry

record Point (R : Set) : Set where
  constructor point
  field
    firstCoordinate  : R
    secondCoordinate : R

open Point

addPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
addPoint reals p q =
  point
    (add reals
      (firstCoordinate p)
      (firstCoordinate q))
    (add reals
      (secondCoordinate p)
      (secondCoordinate q))

scalePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R
scalePoint reals scalar p =
  point
    (multiply reals scalar (firstCoordinate p))
    (multiply reals scalar (secondCoordinate p))

subtractPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
subtractPoint reals p q =
  point
    (subtract reals
      (firstCoordinate p)
      (firstCoordinate q))
    (subtract reals
      (secondCoordinate p)
      (secondCoordinate q))

squaredDistance :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R
squaredDistance reals p q =
  add reals
    (square reals
      (subtract reals
        (firstCoordinate p)
        (firstCoordinate q)))
    (square reals
      (subtract reals
        (secondCoordinate p)
        (secondCoordinate q)))

pointOnSegment :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  R ->
  Point R
pointOnSegment reals p q parameter =
  addPoint reals p
    (scalePoint reals parameter
      (subtractPoint reals q p))

ChordIntersectsUnitDisk :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R ->
  Set
ChordIntersectsUnitDisk {R} reals r p q =
  Exists R
    (\ parameter ->
      InClosedInterval reals
        (zeroR reals)
        (oneR reals)
        parameter
      and
      lessOrEqual reals
        (squaredDistance reals
          (pointOnSegment reals p q parameter)
          (point r (zeroR reals)))
        (oneR reals))

Region : Set -> Set1
Region R =
  Point R -> Set

Empty :
  {R : Set} ->
  Region R
Empty _ =
  Bottom

Complement :
  {R : Set} ->
  Region R ->
  Region R
Complement body p =
  Not (body p)

Intersect :
  {R : Set} ->
  Region R ->
  Region R ->
  Region R
Intersect leftBody rightBody p =
  leftBody p and rightBody p

UnionAll :
  {R : Set} ->
  (Nat -> Region R) ->
  Region R
UnionAll bodies p =
  Exists Nat (\ n -> bodies n p)

Disjoint :
  {R : Set} ->
  Region R ->
  Region R ->
  Set
Disjoint {R} leftBody rightBody =
  (p : Point R) ->
  leftBody p ->
  rightBody p ->
  Bottom

PairwiseDisjoint :
  {R : Set} ->
  (Nat -> Region R) ->
  Set
PairwiseDisjoint bodies =
  (m n : Nat) ->
  m != n ->
  Disjoint (bodies m) (bodies n)

translateRegion :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Region R ->
  Region R
translateRegion {R} reals offset body p =
  Exists (Point R)
    (\ q ->
      body q
      and
      p == addPoint reals offset q)

HalfOpenBox :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Region R
HalfOpenBox reals lower upper p =
  (lessOrEqual reals
    (firstCoordinate lower)
    (firstCoordinate p)
  and
  StrictLess reals
    (firstCoordinate p)
    (firstCoordinate upper))
  and
  (lessOrEqual reals
    (secondCoordinate lower)
    (secondCoordinate p)
  and
  StrictLess reals
    (secondCoordinate p)
    (secondCoordinate upper))

data ExtendedNonnegative (R : Set) : Set where
  finite   : R -> ExtendedNonnegative R
  infinity : ExtendedNonnegative R

data ExtendedLessOrEqual
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  ExtendedNonnegative R ->
  ExtendedNonnegative R ->
  Set where

  finite<=finite :
    {x y : R} ->
    lessOrEqual reals x y ->
    ExtendedLessOrEqual reals (finite x) (finite y)

  finite<=infinity :
    {x : R} ->
    ExtendedLessOrEqual reals (finite x) infinity

  infinity<=infinity :
    ExtendedLessOrEqual reals infinity infinity

addExtended :
  {R : Set} ->
  CompleteOrderedRealField R ->
  ExtendedNonnegative R ->
  ExtendedNonnegative R ->
  ExtendedNonnegative R
addExtended reals infinity rightValue =
  infinity
addExtended reals (finite x) infinity =
  infinity
addExtended reals (finite x) (finite y) =
  finite (add reals x y)

sumFirstExtended :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Nat ->
  (Nat -> ExtendedNonnegative R) ->
  ExtendedNonnegative R
sumFirstExtended reals zero term =
  finite (zeroR reals)
sumFirstExtended reals (suc n) term =
  addExtended reals
    (sumFirstExtended reals n term)
    (term n)

UpperBoundExtended :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> ExtendedNonnegative R) ->
  ExtendedNonnegative R ->
  Set
UpperBoundExtended reals values bound =
  (n : Nat) ->
  ExtendedLessOrEqual reals (values n) bound

LeastUpperBoundExtended :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> ExtendedNonnegative R) ->
  ExtendedNonnegative R ->
  Set
LeastUpperBoundExtended reals values supremum =
  UpperBoundExtended reals values supremum
  and
  ((upper : ExtendedNonnegative _) ->
    UpperBoundExtended reals values upper ->
    ExtendedLessOrEqual reals supremum upper)

record StandardPlaneLebesgueMeasure
  {R : Set}
  (reals : CompleteOrderedRealField R) :
  Set1 where

  field
    measurable : Region R -> Set
    volume : Region R -> ExtendedNonnegative R

    measurable-empty :
      measurable Empty
    measurable-complement :
      (body : Region R) ->
      measurable body ->
      measurable (Complement body)
    measurable-countable-union :
      (bodies : Nat -> Region R) ->
      ((n : Nat) -> measurable (bodies n)) ->
      measurable (UnionAll bodies)
    measurable-intersection :
      (leftBody rightBody : Region R) ->
      measurable leftBody ->
      measurable rightBody ->
      measurable (Intersect leftBody rightBody)
    measurable-translation :
      (offset : Point R) ->
      (body : Region R) ->
      measurable body ->
      measurable (translateRegion reals offset body)
    measurable-box :
      (lower upper : Point R) ->
      measurable (HalfOpenBox reals lower upper)

    volume-congruent :
      (leftBody rightBody : Region R) ->
      ((p : Point R) ->
        Iff (leftBody p) (rightBody p)) ->
      volume leftBody == volume rightBody
    volume-empty :
      volume Empty == finite (zeroR reals)
    volume-nonnegative :
      (body : Region R) ->
      measurable body ->
      ExtendedLessOrEqual reals
        (finite (zeroR reals))
        (volume body)
    volume-countable-additive :
      (bodies : Nat -> Region R) ->
      ((n : Nat) -> measurable (bodies n)) ->
      PairwiseDisjoint bodies ->
      LeastUpperBoundExtended reals
        (\ count ->
          sumFirstExtended reals count
            (\ n -> volume (bodies n)))
        (volume (UnionAll bodies))
    volume-translation-invariant :
      (offset : Point R) ->
      (body : Region R) ->
      measurable body ->
      volume (translateRegion reals offset body) ==
      volume body
    volume-box :
      (lower upper : Point R) ->
      lessOrEqual reals
        (firstCoordinate lower)
        (firstCoordinate upper) ->
      lessOrEqual reals
        (secondCoordinate lower)
        (secondCoordinate upper) ->
      volume (HalfOpenBox reals lower upper) ==
      finite
        (multiply reals
          (subtract reals
            (firstCoordinate upper)
            (firstCoordinate lower))
          (subtract reals
            (secondCoordinate upper)
            (secondCoordinate lower)))

open StandardPlaneLebesgueMeasure

module Putnam2024A5Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (trigonometry : StandardTrigonometry reals)
  (lebesgue : StandardPlaneLebesgueMeasure reals) where

  twoPi : R
  twoPi =
    multiply reals
      (fromNat reals twoN)
      (pi trigonometry)

  circlePoint : R -> Point R
  circlePoint parameter =
    point
      (multiply reals
        (fromNat reals nineN)
        (cosine trigonometry
          (multiply reals twoPi parameter)))
      (multiply reals
        (fromNat reals nineN)
        (sine trigonometry
          (multiply reals twoPi parameter)))

  IntersectionEvent :
    (R -> Point R -> Point R -> Set) ->
    R ->
    Region R
  IntersectionEvent isIntersecting r parameters =
    InClosedInterval reals
      (zeroR reals)
      (oneR reals)
      (firstCoordinate parameters)
    and
    InClosedInterval reals
      (zeroR reals)
      (oneR reals)
      (secondCoordinate parameters)
    and
    isIntersecting r
      (circlePoint (firstCoordinate parameters))
      (circlePoint (secondCoordinate parameters))

  IsMinimumOnAllowedInterval :
    (R -> ExtendedNonnegative R) ->
    R ->
    Set
  IsMinimumOnAllowedInterval probability r =
    InClosedInterval reals
      (zeroR reals)
      (fromNat reals eightN)
      r
    and
    ((x : R) ->
      InClosedInterval reals
        (zeroR reals)
        (fromNat reals eightN)
        x ->
      ExtendedLessOrEqual reals
        (probability r)
        (probability x))

  proposition : Set1
  proposition =
    (isIntersecting : R -> Point R -> Point R -> Set) ->
    ((r : R) ->
      (p q : Point R) ->
      Iff
        (isIntersecting r p q)
        (ChordIntersectsUnitDisk reals r p q)) ->
    (probabilityOfIntersection : R -> ExtendedNonnegative R) ->
    ((r : R) ->
      probabilityOfIntersection r ==
      volume lebesgue
        (IntersectionEvent isIntersecting r)) ->
    (r : R) ->
    Iff
      (IsMinimumOnAllowedInterval
        probabilityOfIntersection
        r)
      (r == zeroR reals)

putnam-2024-a5 : Set1
putnam-2024-a5 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (trigonometry : StandardTrigonometry reals) ->
  (lebesgue : StandardPlaneLebesgueMeasure reals) ->
  Putnam2024A5Statement.proposition
    reals trigonometry lebesgue
