-- Statement-only formalization of PutnamBench corpus artifact putnam_1966_a2:
-- for a noncollinear real triangle with inradius r and semiperimeter p, the sum
-- of the reciprocal squares of p minus each side length is at least 1 / r squared.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

_!=_ : {A : Set} -> A -> A -> Set
x != y = Not (x == y)

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

record ExistsUniqueBy
  (A : Set)
  (equal : A -> A -> Set)
  (P : A -> Set) :
  Set where

  constructor unique-witness
  field
    unique-value : A
    unique-property : P unique-value
    uniqueness :
      (other : A) ->
      P other ->
      equal other unique-value

record CompleteOrderedRealField (R : Set) : Set1 where
  field
    zeroR oneR : R
    addR multiplyR : R -> R -> R
    negateR inverseR squareRootR : R -> R
    lessOrEqualR : R -> R -> Set
    fromNatR : Nat -> R

    oneR-not-zeroR :
      oneR != zeroR

    addR-commutative :
      (x y : R) -> addR x y == addR y x
    addR-associative :
      (x y z : R) -> addR (addR x y) z == addR x (addR y z)
    addR-zero :
      (x : R) -> addR x zeroR == x
    addR-inverse :
      (x : R) -> addR x (negateR x) == zeroR

    multiplyR-commutative :
      (x y : R) -> multiplyR x y == multiplyR y x
    multiplyR-associative :
      (x y z : R) ->
      multiplyR (multiplyR x y) z == multiplyR x (multiplyR y z)
    multiplyR-one :
      (x : R) -> multiplyR x oneR == x
    multiplyR-zero :
      (x : R) -> multiplyR x zeroR == zeroR
    distributeR :
      (x y z : R) ->
      multiplyR x (addR y z) ==
      addR (multiplyR x y) (multiplyR x z)
    inverseR-zero :
      inverseR zeroR == zeroR
    multiplyR-inverse :
      (x : R) ->
      x != zeroR ->
      multiplyR x (inverseR x) == oneR

    order-reflexive :
      (x : R) -> lessOrEqualR x x
    order-transitive :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y z ->
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) ->
      lessOrEqualR x y ->
      lessOrEqualR y x ->
      x == y
    order-total :
      (x y : R) ->
      lessOrEqualR x y or lessOrEqualR y x
    addR-order :
      (x y z : R) ->
      lessOrEqualR x y ->
      lessOrEqualR (addR z x) (addR z y)
    multiplyR-nonnegative :
      (x y : R) ->
      lessOrEqualR zeroR x ->
      lessOrEqualR zeroR y ->
      lessOrEqualR zeroR (multiplyR x y)
    zeroR-less-than-oneR :
      lessOrEqualR zeroR oneR and zeroR != oneR

    fromNatR-zero :
      fromNatR zero == zeroR
    fromNatR-successor :
      (n : Nat) -> fromNatR (suc n) == addR (fromNatR n) oneR
    fromNatR-addition :
      (m n : Nat) ->
      fromNatR (m + n) == addR (fromNatR m) (fromNatR n)
    fromNatR-multiplication :
      (m n : Nat) ->
      fromNatR (m * n) == multiplyR (fromNatR m) (fromNatR n)
    fromNatR-injective :
      (m n : Nat) ->
      fromNatR m == fromNatR n ->
      m == n

    archimedean :
      (x : R) ->
      Exists Nat (\ n -> lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R -> Set) ->
      Exists R P ->
      Exists R
        (\ upper ->
          (x : R) ->
          P x ->
          lessOrEqualR x upper) ->
      Exists R
        (\ supremum ->
          ((x : R) -> P x -> lessOrEqualR x supremum)
          and
          ((upper : R) ->
            ((x : R) -> P x -> lessOrEqualR x upper) ->
            lessOrEqualR supremum upper))

    square-root-nonnegative :
      (x : R) ->
      lessOrEqualR zeroR (squareRootR x)
    square-root-square :
      (x : R) ->
      lessOrEqualR zeroR x ->
      multiplyR (squareRootR x) (squareRootR x) == x
    square-root-nonpositive :
      (x : R) ->
      lessOrEqualR x zeroR ->
      squareRootR x == zeroR
    square-root-unique :
      (x y : R) ->
      lessOrEqualR zeroR y ->
      multiplyR y y == x ->
      y == squareRootR x

open CompleteOrderedRealField

subtract :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
subtract reals x y =
  addR reals x (negateR reals y)

divide :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R
divide reals x y =
  multiplyR reals x (inverseR reals y)

square :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
square reals x =
  multiplyR reals x x

two :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R
two reals =
  addR reals (oneR reals) (oneR reals)

Nonnegative :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqualR reals (zeroR reals) x

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
  addR reals
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
  squareRootR reals (squaredDistance reals p q)

doubleSignedArea :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R
doubleSignedArea reals a b c =
  subtract reals
    (multiplyR reals
      (subtract reals (x-coordinate b) (x-coordinate a))
      (subtract reals (y-coordinate c) (y-coordinate a)))
    (multiplyR reals
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
  doubleSignedArea reals a b c == zeroR reals

weightedPoint :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R ->
  R ->
  Point R ->
  Point R ->
  Point R ->
  Point R
weightedPoint reals alpha beta gamma a b c =
  point
    (addR reals
      (addR reals
        (multiplyR reals alpha (x-coordinate a))
        (multiplyR reals beta (x-coordinate b)))
      (multiplyR reals gamma (x-coordinate c)))
    (addR reals
      (addR reals
        (multiplyR reals alpha (y-coordinate a))
        (multiplyR reals beta (y-coordinate b)))
      (multiplyR reals gamma (y-coordinate c)))

InTriangleConvexHull :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
InTriangleConvexHull {R} reals a b c z =
  Exists R
    (\ alpha ->
      Exists R
        (\ beta ->
          Exists R
            (\ gamma ->
              Nonnegative reals alpha
              and
              Nonnegative reals beta
              and
              Nonnegative reals gamma
              and
              addR reals (addR reals alpha beta) gamma == oneR reals
              and
              PointEqual z
                (weightedPoint reals alpha beta gamma a b c))))

SideContact :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Point R ->
  Point R ->
  Set
SideContact reals center radius a b contact =
  distance reals center contact == radius
  and
  Collinear reals contact a b

UniqueSideContact :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  R ->
  Point R ->
  Point R ->
  Set
UniqueSideContact {R} reals center radius a b =
  ExistsUniqueBy
    (Point R)
    PointEqual
    (SideContact reals center radius a b)

HasInradius :
  {R : Set} ->
  CompleteOrderedRealField R ->
  Point R ->
  Point R ->
  Point R ->
  R ->
  Set
HasInradius {R} reals a b c radius =
  Exists (Point R)
    (\ center ->
      UniqueSideContact reals center radius b c
      and
      UniqueSideContact reals center radius c a
      and
      UniqueSideContact reals center radius a b
      and
      ((z : Point R) ->
        lessOrEqualR reals (distance reals center z) radius ->
        InTriangleConvexHull reals a b c z))

reciprocalSquare :
  {R : Set} ->
  CompleteOrderedRealField R ->
  R ->
  R
reciprocalSquare reals x =
  divide reals (oneR reals) (square reals x)

module Putnam1966A2Statement
  {R : Set}
  (reals : CompleteOrderedRealField R) where

  proposition : Set
  proposition =
    (r : R) ->
    (A B C : Point R) ->
    Not (Collinear reals A B C) ->
    (a b c p : R) ->
    a == distance reals B C ->
    b == distance reals C A ->
    c == distance reals A B ->
    p ==
      divide reals
        (addR reals
          (addR reals
            (distance reals B C)
            (distance reals C A))
          (distance reals A B))
        (two reals) ->
    HasInradius reals A B C r ->
    lessOrEqualR reals
      (reciprocalSquare reals r)
      (addR reals
        (addR reals
          (reciprocalSquare reals (subtract reals p a))
          (reciprocalSquare reals (subtract reals p b)))
        (reciprocalSquare reals (subtract reals p c)))

putnam-1966-a2 : Set1
putnam-1966-a2 =
  (R : Set) ->
  (reals : CompleteOrderedRealField R) ->
  Putnam1966A2Statement.proposition reals
