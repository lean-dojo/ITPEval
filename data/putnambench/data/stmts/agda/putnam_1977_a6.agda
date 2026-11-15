-- Statement-only formalization of PutnamBench corpus artifact putnam_1977_a6:
-- vanishing integrals over every maximal axis-parallel square centered in the
-- unit square force a continuous real function to vanish there; the answer is
-- true. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_ _<=N_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

record Top : Set where
  constructor top

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

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Predicate : Set -> Set1
Predicate A =
  A -> Set

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

PairClose :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Set
PairClose reals center radius p =
  CloseTo reals
    (x-coordinate center)
    radius
    (x-coordinate p)
  and
  CloseTo reals
    (y-coordinate center)
    radius
    (y-coordinate p)

Continuous :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  Set
Continuous {R} reals function =
  (center : Point R) ->
  (epsilon : R) ->
  StrictLess reals (zeroR reals) epsilon ->
  Exists R
    (\ delta ->
      StrictLess reals (zeroR reals) delta
      and
      ((p : Point R) ->
        PairClose reals center delta p ->
        CloseTo reals
          (function center)
          epsilon
          (function p)))

natIndex :
  {n : Nat} ->
  Fin n ->
  Nat
natIndex fzero =
  zero
natIndex (fsuc i) =
  suc (natIndex i)

sumFin :
  {R : Set} ->
  CompleteOrderedRealField R ->
  {n : Nat} ->
  (Fin n -> R) ->
  R
sumFin reals {zero} term =
  zeroR reals
sumFin reals {suc n} term =
  add reals
    (term fzero)
    (sumFin reals (\ i -> term (fsuc i)))

gridPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (lower upper : R) ->
  {n : Nat} ->
  Fin n ->
  R
gridPoint reals lower upper {n} i =
  add reals
    lower
    (multiply reals
      (divide reals
        (subtract reals upper lower)
        (fromNat reals n))
      (fromNat reals (natIndex i)))

rectangleRiemannSum :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  R ->
  R ->
  R ->
  R ->
  Nat ->
  R
rectangleRiemannSum reals function
  lowerX upperX lowerY upperY n =
  multiply reals
    (multiply reals
      (divide reals
        (subtract reals upperX lowerX)
        (fromNat reals n))
      (divide reals
        (subtract reals upperY lowerY)
        (fromNat reals n)))
    (sumFin reals {n = n}
      (\ i ->
        sumFin reals {n = n}
          (\ j ->
            function
              (point
                (gridPoint reals lowerX upperX i)
                (gridPoint reals lowerY upperY j)))))

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

RectangleIntegral :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  R ->
  R ->
  R ->
  R ->
  R ->
  Set
RectangleIntegral reals function
  lowerX upperX lowerY upperY value =
  ConvergesTo reals
    (\ n ->
      rectangleRiemannSum reals function
        lowerX upperX lowerY upperY (suc n))
    value

UnitSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate (Point R)
UnitSquare reals p =
  lessOrEqual reals (zeroR reals) (x-coordinate p)
  and
  lessOrEqual reals (x-coordinate p) (oneR reals)
  and
  lessOrEqual reals (zeroR reals) (y-coordinate p)
  and
  lessOrEqual reals (y-coordinate p) (oneR reals)

RoomValue :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Set
RoomValue reals p radius =
  lessOrEqual reals radius (x-coordinate p)
  and
  lessOrEqual reals radius
    (subtract reals (oneR reals) (x-coordinate p))
  and
  lessOrEqual reals radius (y-coordinate p)
  and
  lessOrEqual reals radius
    (subtract reals (oneR reals) (y-coordinate p))
  and
  (radius == x-coordinate p
  or
  radius == subtract reals (oneR reals) (x-coordinate p)
  or
  radius == y-coordinate p
  or
  radius == subtract reals (oneR reals) (y-coordinate p))

SetMatchesUnitSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate (Point R) ->
  Set
SetMatchesUnitSquare {R} reals X =
  (p : Point R) ->
  Iff (X p) (UnitSquare reals p)

RoomMatchesDefinition :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  Set
RoomMatchesDefinition {R} reals room =
  (p : Point R) ->
  RoomValue reals p (room p)

CenteredSquareIntegralIsZero :
  {R : Set} ->
  CompleteOrderedRealField R ->
  (Point R -> R) ->
  (Point R -> R) ->
  Point R ->
  Set
CenteredSquareIntegralIsZero reals room function p =
  RectangleIntegral reals function
    (subtract reals (x-coordinate p) (room p))
    (add reals (x-coordinate p) (room p))
    (subtract reals (y-coordinate p) (room p))
    (add reals (y-coordinate p) (room p))
    (zeroR reals)

PutnamImplication :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Predicate (Point R) ->
  (Point R -> R) ->
  Set
PutnamImplication {R} reals X room =
  (function : Point R -> R) ->
  Continuous reals function ->
  ((p : Point R) ->
    X p ->
    CenteredSquareIntegralIsZero
      reals room function p) ->
  (p : Point R) ->
  X p ->
  function p == zeroR reals

putnam-1977-a6-solution : Set
putnam-1977-a6-solution =
  Top

putnam-1977-a6 : Set1
putnam-1977-a6 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  (X : Predicate (Point R)) ->
  SetMatchesUnitSquare reals X ->
  (room : Point R -> R) ->
  RoomMatchesDefinition reals room ->
  Iff
    (PutnamImplication reals X room)
    putnam-1977-a6-solution
