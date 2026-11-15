-- Statement-only formalization of "Feuerbach's Theorem" from Hundred Theorems item 029.
-- In the real Euclidean plane, the circle through a nondegenerate triangle's side
-- midpoints is tangent to any circle tangent to its three side lines.
-- This file contains no proof.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not : Set -> Set
Not A = A -> Bottom

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
    value      : A
    property   : P value
    uniqueness : (other : A) -> P other -> equal other value

data NatLe : Nat -> Nat -> Set where
  zero-le : (n : Nat) -> NatLe zero n
  suc-le  : {m n : Nat} -> NatLe m n -> NatLe (suc m) (suc n)

two : Nat
two = suc (suc zero)

powTwo : Nat -> Nat
powTwo zero = suc zero
powTwo (suc n) = two * powTwo n

record Integer : Set where
  constructor integer
  field
    positive : Nat
    negative : Nat

open Integer

integerZero : Integer
integerZero = integer zero zero

integerFromNat : Nat -> Integer
integerFromNat n = integer n zero

integerAdd : Integer -> Integer -> Integer
integerAdd x y =
  integer
    (positive x + positive y)
    (negative x + negative y)

integerNegate : Integer -> Integer
integerNegate x =
  integer (negative x) (positive x)

integerSubtract : Integer -> Integer -> Integer
integerSubtract x y =
  integerAdd x (integerNegate y)

integerMultiply : Integer -> Integer -> Integer
integerMultiply x y =
  integer
    ((positive x * positive y) + (negative x * negative y))
    ((positive x * negative y) + (negative x * positive y))

integerScale : Nat -> Integer -> Integer
integerScale n x =
  integer (n * positive x) (n * negative x)

IntegerLe : Integer -> Integer -> Set
IntegerLe x y =
  NatLe
    (positive x + negative y)
    (positive y + negative x)

IntegerClose : Nat -> Nat -> Integer -> Integer -> Set
IntegerClose denominatorPower precision x y =
  IntegerLe
    (integerNegate (integerFromNat (powTwo denominatorPower)))
    (integerScale (powTwo precision) (integerSubtract x y))
  and
  IntegerLe
    (integerScale (powTwo precision) (integerSubtract x y))
    (integerFromNat (powTwo denominatorPower))

CauchySequence : (Nat -> Integer) -> Set
CauchySequence approximation =
  (precision : Nat) ->
  Exists Nat
    (\ threshold ->
      (m n : Nat) ->
      NatLe threshold m ->
      NatLe threshold n ->
      IntegerClose
        (m + n)
        precision
        (integerSubtract
          (integerScale (powTwo n) (approximation m))
          (integerScale (powTwo m) (approximation n)))
        integerZero)

record Real : Set where
  constructor real
  field
    approximation : Nat -> Integer
    cauchy         : CauchySequence approximation

open Real

SequenceEqual :
  (Nat -> Nat) ->
  (Nat -> Integer) ->
  (Nat -> Integer) ->
  Set
SequenceEqual denominatorPower x y =
  (precision : Nat) ->
  Exists Nat
    (\ threshold ->
      (n : Nat) ->
      NatLe threshold n ->
      IntegerClose (denominatorPower n) precision (x n) (y n))

LinearEqual :
  (Nat -> Integer) ->
  (Nat -> Integer) ->
  Set
LinearEqual =
  SequenceEqual (\ n -> n)

QuadraticEqual :
  (Nat -> Integer) ->
  (Nat -> Integer) ->
  Set
QuadraticEqual =
  SequenceEqual (\ n -> n + n)

RealEqual : Real -> Real -> Set
RealEqual x y =
  LinearEqual (approximation x) (approximation y)

StrictlyNegative : Real -> Set
StrictlyNegative x =
  Exists Nat
    (\ precision ->
      Exists Nat
        (\ threshold ->
          (n : Nat) ->
          NatLe threshold n ->
          IntegerLe
            (integerAdd
              (integerScale
                (powTwo precision)
                (approximation x n))
              (integerFromNat (powTwo n)))
            integerZero))

Nonnegative : Real -> Set
Nonnegative x =
  Not (StrictlyNegative x)

record Point : Set where
  constructor point
  field
    x-coordinate : Real
    y-coordinate : Real

open Point

PointEqual : Point -> Point -> Set
PointEqual p q =
  RealEqual (x-coordinate p) (x-coordinate q)
  and
  RealEqual (y-coordinate p) (y-coordinate q)

zeroSequence : Nat -> Integer
zeroSequence n =
  integerZero

xDifference : Point -> Point -> Nat -> Integer
xDifference p q n =
  integerSubtract
    (approximation (x-coordinate p) n)
    (approximation (x-coordinate q) n)

yDifference : Point -> Point -> Nat -> Integer
yDifference p q n =
  integerSubtract
    (approximation (y-coordinate p) n)
    (approximation (y-coordinate q) n)

squaredDistanceNumerator : Point -> Point -> Nat -> Integer
squaredDistanceNumerator p q n =
  integerAdd
    (integerMultiply (xDifference p q n) (xDifference p q n))
    (integerMultiply (yDifference p q n) (yDifference p q n))

radiusSquareNumerator : Real -> Nat -> Integer
radiusSquareNumerator radius n =
  integerMultiply
    (approximation radius n)
    (approximation radius n)

Midpoint : Point -> Point -> Point -> Set
Midpoint a b midpoint =
  LinearEqual
    (\ n ->
      integerScale two
        (approximation (x-coordinate midpoint) n))
    (\ n ->
      integerAdd
        (approximation (x-coordinate a) n)
        (approximation (x-coordinate b) n))
  and
  LinearEqual
    (\ n ->
      integerScale two
        (approximation (y-coordinate midpoint) n))
    (\ n ->
      integerAdd
        (approximation (y-coordinate a) n)
        (approximation (y-coordinate b) n))

determinantNumerator : Point -> Point -> Point -> Nat -> Integer
determinantNumerator a b c n =
  integerSubtract
    (integerMultiply
      (xDifference a b n)
      (yDifference c b n))
    (integerMultiply
      (yDifference a b n)
      (xDifference c b n))

Collinear : Point -> Point -> Point -> Set
Collinear a b c =
  QuadraticEqual
    (determinantNumerator a b c)
    zeroSequence

dotProductNumerator :
  Point ->
  Point ->
  Point ->
  Point ->
  Nat ->
  Integer
dotProductNumerator a b c d n =
  integerAdd
    (integerMultiply
      (xDifference a b n)
      (xDifference c d n))
    (integerMultiply
      (yDifference a b n)
      (yDifference c d n))

Orthogonal : Point -> Point -> Point -> Point -> Set
Orthogonal a b c d =
  QuadraticEqual
    (dotProductNumerator a b c d)
    zeroSequence

OnCircle : Point -> Real -> Point -> Set
OnCircle center radius p =
  Nonnegative radius
  and
  QuadraticEqual
    (squaredDistanceNumerator center p)
    (radiusSquareNumerator radius)

CirclesTangent : Point -> Real -> Point -> Real -> Set
CirclesTangent center1 radius1 center2 radius2 =
  (PointEqual center1 center2 and RealEqual radius1 radius2)
  or
  ExistsUniqueBy Point PointEqual
    (\ p ->
      OnCircle center1 radius1 p
      and
      OnCircle center2 radius2 p)

feuerbachs-theorem : Set
feuerbachs-theorem =
  (a b c mbc mac mab pbc pac pab ncenter icenter : Point) ->
  (nradius iradius : Real) ->
  Not (Collinear a b c) ->
  Midpoint a b mab ->
  Midpoint b c mbc ->
  Midpoint c a mac ->
  OnCircle ncenter nradius mbc ->
  OnCircle ncenter nradius mac ->
  OnCircle ncenter nradius mab ->
  OnCircle icenter iradius pbc ->
  OnCircle icenter iradius pac ->
  OnCircle icenter iradius pab ->
  Collinear a b pab ->
  Orthogonal a b icenter pab ->
  Collinear b c pbc ->
  Orthogonal b c icenter pbc ->
  Collinear a c pac ->
  Orthogonal a c icenter pac ->
  CirclesTangent ncenter nradius icenter iradius
