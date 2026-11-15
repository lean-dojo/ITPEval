-- Statement-only formalization of PutnamBench corpus artifact putnam_1991_a4:
-- an infinite sequence of closed discs has locally finite centers, finite total
-- area, and meets every line in the real plane. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_ _<N_
infixr 1 _iff_
infixr 3 _and_
infixr 2 _or_

data Top : Set where
  trivial : Top

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record _iff_ (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A -> B
    backward : B -> A

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
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

_<N_ : Nat -> Nat -> Set
m <N n =
  suc m <=N n

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
  (Nat -> R) ->
  Nat ->
  R
sumFirst reals terms zero =
  zeroR reals
sumFirst reals terms (suc n) =
  add reals
    (sumFirst reals terms n)
    (terms n)

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

SeriesConvergent :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
SeriesConvergent reals terms =
  Exists _
    (\ limit ->
      ConvergesTo reals
        (sumFirst reals terms)
        limit)

StrictlyIncreasing :
  (Nat -> Nat) ->
  Set
StrictlyIncreasing subsequence =
  (m n : Nat) ->
  m <N n ->
  subsequence m <N subsequence n

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

zeroPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R
zeroPoint reals =
  point (zeroR reals) (zeroR reals)

addPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R
addPoint reals p q =
  point
    (add reals (x-coordinate p) (x-coordinate q))
    (add reals (y-coordinate p) (y-coordinate q))

scalePoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Point R ->
  Point R
scalePoint reals scalar p =
  point
    (multiply reals scalar (x-coordinate p))
    (multiply reals scalar (y-coordinate p))

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

InOpenBall :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Set
InOpenBall reals center radius p =
  StrictLess reals
    (squaredDistance reals p center)
    (square reals radius)

InClosedDisc :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Set
InClosedDisc reals center radius p =
  lessOrEqual reals
    (squaredDistance reals p center)
    (square reals radius)

ClusterPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> Point R) ->
  Point R ->
  Set
ClusterPoint reals centers p =
  (epsilon : _) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists (Nat -> Nat)
    (\ subsequence ->
      StrictlyIncreasing subsequence
      and
      ((i : Nat) ->
        InOpenBall reals
          p
          epsilon
          (centers (subsequence i))))

NoFiniteLimitPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> Point R) ->
  Set
NoFiniteLimitPoint {R} reals centers =
  Not
    (Exists (Point R)
      (ClusterPoint reals centers))

NonnegativeRadii :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
NonnegativeRadii reals radii =
  (i : Nat) ->
  lessOrEqual reals (zeroR reals) (radii i)

FiniteTotalArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> R) ->
  Set
FiniteTotalArea reals radii =
  SeriesConvergent reals
    (\ i -> square reals (radii i))

MeetsEveryLine :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Nat -> Point R) ->
  (Nat -> R) ->
  Set
MeetsEveryLine reals centers radii =
  (base direction : Point _) ->
  direction != zeroPoint reals ->
  Exists Nat
    (\ i ->
      Exists _
        (\ t ->
          InClosedDisc reals
            (centers i)
            (radii i)
            (addPoint reals
              base
              (scalePoint reals t direction))))

DiskSequenceExists :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Set
DiskSequenceExists {R} reals =
  Exists (Nat -> Point R)
    (\ centers ->
      Exists (Nat -> R)
        (\ radii ->
          NonnegativeRadii reals radii
          and
          NoFiniteLimitPoint reals centers
          and
          FiniteTotalArea reals radii
          and
          MeetsEveryLine reals centers radii))

putnam-1991-a4-solution : Set
putnam-1991-a4-solution =
  Top

putnam-1991-a4 : Set1
putnam-1991-a4 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  DiskSequenceExists reals iff putnam-1991-a4-solution
