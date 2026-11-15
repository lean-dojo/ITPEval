-- Statement-only formalization of "Morley's Theorem" from Hundred Theorems item 084.
-- In the real Euclidean plane, the intersections of adjacent internal angle
-- trisectors of a nondegenerate triangle form an equilateral triangle.
-- This file contains no proof.

module HundredTheorems084 where

open import Agda.Builtin.Equality renaming (_≡_ to _==_)

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

data Natural : Set where
  natZero : Natural
  natSuc  : Natural -> Natural

record CompleteOrderedField (R : Set) : Set1 where
  field
    zero one : R
    add multiply : R -> R -> R
    negate inverse : R -> R
    lessOrEqual : R -> R -> Set
    fromNat : Natural -> R

    one-not-zero :
      one != zero

    add-commutative :
      (x y : R) -> add x y == add y x
    add-associative :
      (x y z : R) -> add (add x y) z == add x (add y z)
    add-zero :
      (x : R) -> add x zero == x
    add-inverse :
      (x : R) -> add x (negate x) == zero

    multiply-commutative :
      (x y : R) -> multiply x y == multiply y x
    multiply-associative :
      (x y z : R) ->
      multiply (multiply x y) z == multiply x (multiply y z)
    multiply-one :
      (x : R) -> multiply x one == x
    multiply-zero :
      (x : R) -> multiply x zero == zero
    distribute :
      (x y z : R) ->
      multiply x (add y z) ==
      add (multiply x y) (multiply x z)
    multiply-inverse :
      (x : R) ->
      x != zero ->
      multiply x (inverse x) == one
    inverse-zero :
      inverse zero == zero

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
      lessOrEqual zero x ->
      lessOrEqual zero y ->
      lessOrEqual zero (multiply x y)
    zero-less-than-one :
      lessOrEqual zero one and zero != one

    fromNat-zero :
      fromNat natZero == zero
    fromNat-successor :
      (n : Natural) -> fromNat (natSuc n) == add (fromNat n) one
    archimedean :
      (x : R) ->
      Exists Natural (\ n -> lessOrEqual x (fromNat n))
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

StrictLess :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
StrictLess reals x y =
  lessOrEqual reals x y and x != y

Positive :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Positive reals x =
  StrictLess reals (zero reals) x

Nonnegative :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
Nonnegative reals x =
  lessOrEqual reals (zero reals) x

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

xVector :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
xVector reals origin endpoint =
  subtract reals
    (x-coordinate endpoint)
    (x-coordinate origin)

yVector :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
yVector reals origin endpoint =
  subtract reals
    (y-coordinate endpoint)
    (y-coordinate origin)

DotAt :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  R
DotAt reals vertex firstRay secondRay =
  add reals
    (multiply reals
      (xVector reals vertex firstRay)
      (xVector reals vertex secondRay))
    (multiply reals
      (yVector reals vertex firstRay)
      (yVector reals vertex secondRay))

CrossAt :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  R
CrossAt reals vertex firstRay secondRay =
  subtract reals
    (multiply reals
      (xVector reals vertex firstRay)
      (yVector reals vertex secondRay))
    (multiply reals
      (yVector reals vertex firstRay)
      (xVector reals vertex secondRay))

SquaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
SquaredDistance reals p q =
  add reals
    (square reals (xVector reals p q))
    (square reals (yVector reals p q))

Noncollinear :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Noncollinear reals a b c =
  CrossAt reals a b c != zero reals

-- Barycentric membership is the target-native form of membership in the
-- convex hull of the three vertices.
TriangleHullMember :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
TriangleHullMember {R} reals a b c p =
  Exists R
    (\ alpha ->
      Exists R
        (\ beta ->
          Exists R
            (\ gamma ->
              Nonnegative reals alpha
              and Nonnegative reals beta
              and Nonnegative reals gamma
              and add reals alpha (add reals beta gamma) == one reals
              and x-coordinate p ==
                add reals
                  (multiply reals alpha (x-coordinate a))
                  (add reals
                    (multiply reals beta (x-coordinate b))
                    (multiply reals gamma (x-coordinate c)))
              and y-coordinate p ==
                add reals
                  (multiply reals alpha (y-coordinate a))
                  (add reals
                    (multiply reals beta (y-coordinate b))
                    (multiply reals gamma (y-coordinate c))))))

SameDirectedAngle :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
SameDirectedAngle {R} reals vertex a b c d =
  Exists R
    (\ scale ->
      Positive reals scale
      and
      DotAt reals vertex a b ==
        multiply reals scale (DotAt reals vertex c d)
      and
      CrossAt reals vertex a b ==
        multiply reals scale (CrossAt reals vertex c d))

SameNonzeroSign :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
SameNonzeroSign reals x y =
  (Positive reals x and Positive reals y)
  or
  (Positive reals (negate reals x)
   and Positive reals (negate reals y))

TrisectedAngle :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Point R ->
  Set
TrisectedAngle reals vertex firstBoundary firstTrisector secondTrisector secondBoundary =
  firstBoundary != vertex
  and firstTrisector != vertex
  and secondTrisector != vertex
  and secondBoundary != vertex
  and Positive reals
    (DotAt reals vertex firstBoundary firstTrisector)
  and Positive reals
    (DotAt reals vertex firstTrisector secondTrisector)
  and Positive reals
    (DotAt reals vertex secondTrisector secondBoundary)
  and SameNonzeroSign reals
    (CrossAt reals vertex firstBoundary firstTrisector)
    (CrossAt reals vertex firstBoundary secondBoundary)
  and SameDirectedAngle reals
    vertex
    firstBoundary
    firstTrisector
    firstTrisector
    secondTrisector
  and SameDirectedAngle reals
    vertex
    firstTrisector
    secondTrisector
    secondTrisector
    secondBoundary

module MorleyStatement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (a b c p q r : Point R) ->
    Noncollinear reals a b c ->
    TriangleHullMember reals a b c p ->
    TriangleHullMember reals a b c q ->
    TriangleHullMember reals a b c r ->
    TrisectedAngle reals b a r p c ->
    TrisectedAngle reals a b r q c ->
    TrisectedAngle reals c b p q a ->
    SquaredDistance reals r p == SquaredDistance reals p q
    and
    SquaredDistance reals q r == SquaredDistance reals p q

morleys-theorem : Set1
morleys-theorem =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  MorleyStatement.proposition reals
