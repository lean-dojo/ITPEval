-- Statement-only formalization of PutnamBench corpus artifact putnam_1962_b3:
-- boundedness of a convex subset of the real plane that contains the origin
-- and has a point outside it on every ray. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam1962B3 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  Set ->
  Set
Not A =
  A -> Bottom

_!=_ :
  {A : Set} ->
  A ->
  A ->
  Set
x != y =
  Not (x == y)

record _and_
  (A : Set)
  (B : Set) :
  Set where
  constructor both
  field
    first  : A
    second : B

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Exists
  (A : Set)
  (P : A -> Set) :
  Set where
  constructor witness
  field
    value    : A
    property : P value

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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

Subset :
  (R : Set) ->
  Set1
Subset R =
  Point R -> Set

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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

StrictPositive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
StrictPositive reals x =
  StrictLess reals (zeroR reals) x

origin :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R
origin reals =
  point (zeroR reals) (zeroR reals)

scale :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Point R ->
  Point R
scale reals coefficient p =
  point
    (multiply reals coefficient (x-coordinate p))
    (multiply reals coefficient (y-coordinate p))

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
  Subset R ->
  Set
Convex reals S =
  (p q : Point _) ->
  S p ->
  S q ->
  (coefficient : _) ->
  lessOrEqual reals (zeroR reals) coefficient ->
  lessOrEqual reals coefficient (oneR reals) ->
  S (affineCombination reals coefficient p q)

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

OpenBall :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  R ->
  Point R ->
  Set
OpenBall reals center radius p =
  StrictLess reals
    (squaredDistance reals center p)
    (square reals radius)

InteriorMember :
  {R : Set} ->
  CompleteOrderedField R ->
  Subset R ->
  Point R ->
  Set
InteriorMember {R} reals S p =
  Exists R
    (\ radius ->
      StrictPositive reals radius
      and
      ((q : Point R) ->
        OpenBall reals p radius q ->
        S q))

Closed :
  {R : Set} ->
  CompleteOrderedField R ->
  Subset R ->
  Set
Closed {R} reals S =
  (p : Point R) ->
  Not (S p) ->
  Exists R
    (\ radius ->
      StrictPositive reals radius
      and
      ((q : Point R) ->
        OpenBall reals p radius q ->
        Not (S q)))

SameRay :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Set
SameRay {R} reals p q =
  Exists R
    (\ coefficient ->
      StrictPositive reals coefficient
      and
      q == scale reals coefficient p)

Bounded :
  {R : Set} ->
  CompleteOrderedField R ->
  Subset R ->
  Set
Bounded {R} reals S =
  Exists R
    (\ radius ->
      StrictPositive reals radius
      and
      ((p : Point R) ->
        S p ->
        lessOrEqual reals
          (squaredDistance reals (origin reals) p)
          (square reals radius)))

module Putnam1962B3Statement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set1
  proposition =
    (S : Subset R) ->
    (Convex reals S and S (origin reals)) ->
    (InteriorMember reals S (origin reals) or Closed reals S) ->
    ((P : Point R) ->
      P != origin reals ->
      Exists (Point R)
        (\ Q ->
          SameRay reals P Q
          and
          Not (S Q))) ->
    Bounded reals S

putnam-1962-b3 : Set1
putnam-1962-b3 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  Putnam1962B3Statement.proposition reals
