-- Statement-only formalization of PutnamBench corpus artifact putnam_1967_a5:
-- every convex region in the real Euclidean plane with Lebesgue area greater
-- than pi / 4 contains two points at distance exactly one. This file contains no proof.

{-# OPTIONS --safe #-}

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

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<=N_ : Nat -> Nat -> Set where
  zero<=    : {n : Nat} -> zero <=N n
  suc<=suc  : {m n : Nat} -> m <=N n -> suc m <=N suc n

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

open CompleteOrderedField

subtract :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R
square reals x =
  multiply reals x x

divide :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  R
divide reals x y =
  multiply reals x (inverse reals y)

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

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
      StrictLess reals
        (subtract reals limit epsilon)
        (sequence n)
      and
      StrictLess reals
        (sequence n)
        (add reals limit epsilon))

oddNatural : Nat -> Nat
oddNatural zero =
  suc zero
oddNatural (suc n) =
  suc (suc (oddNatural n))

alternatingUnit :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
alternatingUnit reals zero =
  oneR reals
alternatingUnit reals (suc n) =
  negate reals (alternatingUnit reals n)

leibnizTerm :
  {R : Set} ->
  CompleteOrderedField R ->
  Nat ->
  R
leibnizTerm reals n =
  multiply reals
    (alternatingUnit reals n)
    (inverse reals
      (fromNat reals (oddNatural n)))

leibnizPartialSum :
  {R : Set} ->
  CompleteOrderedField R ->
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
  CompleteOrderedField R ->
  Nat ->
  R
piApproximation reals n =
  multiply reals
    (fromNat reals 4)
    (leibnizPartialSum reals n)

record StandardRealPlane (R : Set) : Set1 where
  field
    algebra : CompleteOrderedField R
    pi : R

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Region : Set -> Set1
Region R =
  Point R -> Set

affineCombination :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Point R ->
  Point R ->
  Point R
affineCombination reals coefficient p q =
  point
    (add reals
      (multiply reals coefficient (x-coordinate p))
      (multiply reals
        (subtract reals (oneR reals) coefficient)
        (x-coordinate q)))
    (add reals
      (multiply reals coefficient (y-coordinate p))
      (multiply reals
        (subtract reals (oneR reals) coefficient)
        (y-coordinate q)))

Convex :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  Set
Convex reals body =
  (p q : Point _) ->
  body p ->
  body q ->
  (coefficient : _) ->
  lessOrEqual reals (zeroR reals) coefficient ->
  lessOrEqual reals coefficient (oneR reals) ->
  body (affineCombination reals coefficient p q)

squaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
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

record Rectangle (R : Set) : Set where
  constructor rectangle
  field
    lower-x upper-x : R
    lower-y upper-y : R

open Rectangle

ValidRectangle :
  {R : Set} ->
  CompleteOrderedField R ->
  Rectangle R ->
  Set
ValidRectangle reals box =
  lessOrEqual reals (lower-x box) (upper-x box)
  and
  lessOrEqual reals (lower-y box) (upper-y box)

RectangleContains :
  {R : Set} ->
  CompleteOrderedField R ->
  Rectangle R ->
  Point R ->
  Set
RectangleContains reals box p =
  StrictLess reals (lower-x box) (x-coordinate p)
  and
  StrictLess reals (x-coordinate p) (upper-x box)
  and
  StrictLess reals (lower-y box) (y-coordinate p)
  and
  StrictLess reals (y-coordinate p) (upper-y box)

rectangleArea :
  {R : Set} ->
  CompleteOrderedField R ->
  Rectangle R ->
  R
rectangleArea reals box =
  multiply reals
    (subtract reals (upper-x box) (lower-x box))
    (subtract reals (upper-y box) (lower-y box))

RectangleCover : Set -> Set
RectangleCover R =
  Nat -> Rectangle R

ValidCover :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover R ->
  Set
ValidCover reals cover =
  (n : Nat) ->
  ValidRectangle reals (cover n)

Covers :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover R ->
  Region R ->
  Set
Covers {R} reals cover body =
  (p : Point R) ->
  body p ->
  Exists Nat
    (\ n -> RectangleContains reals (cover n) p)

coverPartialArea :
  {R : Set} ->
  CompleteOrderedField R ->
  RectangleCover R ->
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
  RectangleCover R ->
  R ->
  Set
CoverTotal reals cover total =
  SequentialLimit reals
    (coverPartialArea reals cover)
    total

CoverCost :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  R ->
  Set
CoverCost {R} reals body total =
  Exists (RectangleCover R)
    (\ cover ->
      ValidCover reals cover
      and
      Covers reals cover body
      and
      CoverTotal reals cover total)

LowerBound :
  {R : Set} ->
  CompleteOrderedField R ->
  (R -> Set) ->
  R ->
  Set
LowerBound reals values bound =
  (value : _) ->
  values value ->
  lessOrEqual reals bound value

LebesgueAreaGreaterThan :
  {R : Set} ->
  CompleteOrderedField R ->
  Region R ->
  R ->
  Set
LebesgueAreaGreaterThan {R} reals body threshold =
  Exists R
    (\ lower ->
      StrictLess reals threshold lower
      and
      LowerBound reals (CoverCost reals body) lower)

module Putnam1967A5Statement
  {R : Set}
  (plane : StandardRealPlane R) where

  reals : CompleteOrderedField R
  reals =
    algebra plane

  quarterPi : R
  quarterPi =
    divide reals
      (pi plane)
      (fromNat reals 4)

  proposition : Set1
  proposition =
    (body : Region R) ->
    Convex reals body ->
    LebesgueAreaGreaterThan reals body quarterPi ->
    Exists (Point R)
      (\ P ->
        body P
        and
        Exists (Point R)
          (\ Q ->
            body Q
            and
            squaredDistance reals P Q == oneR reals))

putnam-1967-a5 : Set1
putnam-1967-a5 =
  (R : Set) ->
  (plane : StandardRealPlane R) ->
  Putnam1967A5Statement.proposition plane
