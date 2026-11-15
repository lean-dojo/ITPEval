-- Statement-only formalization of PutnamBench corpus artifact putnam_1996_a2
-- (putnambench__agda__putnam_1996_a2): the midpoint locus determined by
-- circles of radii 1 and 3 whose centers are 10 units apart is the closed
-- annulus of radii 1 and 2 about the centers' midpoint. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_

data Bottom : Set where

Not : Set -> Set
Not A =
  A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y =
  Not (x == y)

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

_and_ : Set -> Set -> Set
A and B =
  Both A B

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

record StandardReal (R : Set) : Set1 where
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
      (x y : R) -> Either (lessOrEqual x y) (lessOrEqual y x)
    add-monotone :
      (x y z : R) ->
      lessOrEqual x y ->
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) ->
      lessOrEqual zeroR x ->
      lessOrEqual zeroR y ->
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR and oneR != zeroR

    fromNat-zero :
      fromNat zero == zeroR
    fromNat-successor :
      (n : Nat) -> fromNat (suc n) == add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) -> fromNat m == fromNat n -> m == n
    fromNat-nonnegative :
      (n : Nat) -> lessOrEqual zeroR (fromNat n)

    square-root-nonnegative :
      (x : R) -> lessOrEqual zeroR (squareRoot x)
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
      squareRoot x == y

    archimedean :
      (x : R) ->
      Exists Nat
        (\ n -> lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) -> P x -> lessOrEqual x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqual x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqual x upper) ->
            lessOrEqual supremum upper))

open StandardReal

subtract :
  {R : Set} ->
  StandardReal R ->
  R ->
  R ->
  R
subtract reals x y =
  add reals x (negate reals y)

square :
  {R : Set} ->
  StandardReal R ->
  R ->
  R
square reals x =
  multiply reals x x

half :
  {R : Set} ->
  StandardReal R ->
  R
half reals =
  inverse reals (fromNat reals 2)

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

SameSubset :
  {R : Set} ->
  Subset R ->
  Subset R ->
  Set
SameSubset {R} A B =
  (p : Point R) ->
  Iff (A p) (B p)

squaredDistance :
  {R : Set} ->
  StandardReal R ->
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
  StandardReal R ->
  Point R ->
  Point R ->
  R
distance reals p q =
  squareRoot reals (squaredDistance reals p q)

midpoint :
  {R : Set} ->
  StandardReal R ->
  Point R ->
  Point R ->
  Point R
midpoint reals p q =
  point
    (multiply reals
      (add reals (x-coordinate p) (x-coordinate q))
      (half reals))
    (multiply reals
      (add reals (y-coordinate p) (y-coordinate q))
      (half reals))

Circle :
  {R : Set} ->
  StandardReal R ->
  Point R ->
  R ->
  Subset R
Circle reals center radius p =
  distance reals p center == radius

MidpointLocus :
  {R : Set} ->
  StandardReal R ->
  Subset R ->
  Subset R ->
  Subset R
MidpointLocus {R} reals C1 C2 M =
  Exists (Point R)
    (\ X ->
      Exists (Point R)
        (\ Y ->
          C1 X
          and
          C2 Y
          and
          M == midpoint reals X Y))

SolutionAnnulus :
  {R : Set} ->
  StandardReal R ->
  Point R ->
  Point R ->
  Subset R
SolutionAnnulus reals O1 O2 p =
  lessOrEqual reals
    (fromNat reals 1)
    (distance reals p (midpoint reals O1 O2))
  and
  lessOrEqual reals
    (distance reals p (midpoint reals O1 O2))
    (fromNat reals 2)

module Putnam1996A2Statement
  {R : Set}
  (reals : StandardReal R) where

  proposition : Set1
  proposition =
    (O1 O2 : Point R) ->
    (C1 C2 : Subset R) ->
    SameSubset C1
      (Circle reals O1 (fromNat reals 1)) ->
    SameSubset C2
      (Circle reals O2 (fromNat reals 3)) ->
    distance reals O1 O2 == fromNat reals 10 ->
    SameSubset
      (MidpointLocus reals C1 C2)
      (SolutionAnnulus reals O1 O2)

putnam-1996-a2 : Set1
putnam-1996-a2 =
  (R : Set) ->
  (reals : StandardReal R) ->
  Putnam1996A2Statement.proposition reals
