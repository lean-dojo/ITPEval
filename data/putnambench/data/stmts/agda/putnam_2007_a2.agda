-- Statement-only formalization of PutnamBench corpus artifact putnam_2007_a2
-- (putnambench__agda__putnam_2007_a2): the least Lebesgue area of a convex
-- planar set meeting both branches of xy = 1 and both branches of xy = -1
-- is four. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2007A2 where

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
  zero<=   : {n : Nat} -> zero <=N n
  suc<=suc : {m n : Nat} -> m <=N n -> suc m <=N suc n

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
    negate-involutive :
      (x : R) -> negate (negate x) == x

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

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

record Point (R : Set) : Set where
  constructor point
  field
    firstCoordinate  : R
    secondCoordinate : R

open Point

Region : Set -> Set1
Region R =
  Point R -> Set

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

linearCombination :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R ->
  Point R
linearCombination reals t p q =
  addPoint reals
    (scalePoint reals t p)
    (scalePoint reals
      (subtract reals (oneR reals) t)
      q)

Convex :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Region R ->
  Set
Convex {R} reals body =
  (p q : Point R) ->
  body p ->
  body q ->
  (t : R) ->
  lessOrEqual reals (zeroR reals) t ->
  lessOrEqual reals t (oneR reals) ->
  body (linearCombination reals t p q)

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
    measurable-translation :
      (offset : Point R) ->
      (body : Region R) ->
      measurable body ->
      measurable (translateRegion reals offset body)
    measurable-box :
      (lower upper : Point R) ->
      measurable (HalfOpenBox reals lower upper)
    convex-measurable :
      (body : Region R) ->
      Convex reals body ->
      measurable body

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

fourN : Nat
fourN =
  suc (suc (suc (suc zero)))

module Putnam2007A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R)
  (lebesgue : StandardPlaneLebesgueMeasure reals) where

  OnPositiveBranchPositiveQuadrant :
    Point R ->
    Set
  OnPositiveBranchPositiveQuadrant p =
    StrictLess reals
      (zeroR reals)
      (firstCoordinate p)
    and
    StrictLess reals
      (zeroR reals)
      (secondCoordinate p)
    and
    multiply reals
      (firstCoordinate p)
      (secondCoordinate p)
      == oneR reals

  OnPositiveBranchNegativeQuadrant :
    Point R ->
    Set
  OnPositiveBranchNegativeQuadrant p =
    StrictLess reals
      (firstCoordinate p)
      (zeroR reals)
    and
    StrictLess reals
      (secondCoordinate p)
      (zeroR reals)
    and
    multiply reals
      (firstCoordinate p)
      (secondCoordinate p)
      == oneR reals

  OnNegativeBranchNorthwest :
    Point R ->
    Set
  OnNegativeBranchNorthwest p =
    StrictLess reals
      (firstCoordinate p)
      (zeroR reals)
    and
    StrictLess reals
      (zeroR reals)
      (secondCoordinate p)
    and
    multiply reals
      (firstCoordinate p)
      (secondCoordinate p)
      == negate reals (oneR reals)

  OnNegativeBranchSoutheast :
    Point R ->
    Set
  OnNegativeBranchSoutheast p =
    StrictLess reals
      (zeroR reals)
      (firstCoordinate p)
    and
    StrictLess reals
      (secondCoordinate p)
      (zeroR reals)
    and
    multiply reals
      (firstCoordinate p)
      (secondCoordinate p)
      == negate reals (oneR reals)

  Meets :
    Region R ->
    (Point R -> Set) ->
    Set
  Meets body locus =
    Exists (Point R)
      (\ p ->
        body p
        and
        locus p)

  Qualifying :
    Region R ->
    Set
  Qualifying body =
    Convex reals body
    and
    Meets body OnPositiveBranchPositiveQuadrant
    and
    Meets body OnPositiveBranchNegativeQuadrant
    and
    Meets body OnNegativeBranchNorthwest
    and
    Meets body OnNegativeBranchSoutheast

  record AttainableArea
    (candidate : ExtendedNonnegative R) :
    Set1 where

    field
      body : Region R
      qualifying : Qualifying body
      has-area : volume lebesgue body == candidate

  record IsLeastArea
    (answer : ExtendedNonnegative R) :
    Set1 where

    field
      attained : AttainableArea answer
      lower-bound :
        (candidate : ExtendedNonnegative R) ->
        AttainableArea candidate ->
        ExtendedLessOrEqual reals answer candidate

  proposition : Set1
  proposition =
    IsLeastArea (finite (fromNat reals fourN))

putnam-2007-a2 : Set1
putnam-2007-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (lebesgue : StandardPlaneLebesgueMeasure reals) ->
  Putnam2007A2Statement.proposition reals lebesgue
