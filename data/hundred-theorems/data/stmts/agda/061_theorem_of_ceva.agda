-- Statement-only formalization of "Theorem of Ceva" from Hundred Theorems item 061:
-- three vertex lines through points on the opposite side lines of a nondegenerate
-- real Euclidean triangle meet at one point only if the corresponding triple
-- products of distances are equal. This file contains no proof.

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

record CompleteOrderedField (R : Set) : Set₁ where
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

record Point (R : Set) : Set where
  constructor point
  field
    x-coordinate : R
    y-coordinate : R

open Point

SquaredDistance :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  R
SquaredDistance reals p q =
  add reals
    (square reals
      (subtract reals (x-coordinate p) (x-coordinate q)))
    (square reals
      (subtract reals (y-coordinate p) (y-coordinate q)))

Collinear :
  {R : Set} ->
  CompleteOrderedField R ->
  Point R ->
  Point R ->
  Point R ->
  Set
Collinear reals a b c =
  subtract reals
    (multiply reals
      (subtract reals (x-coordinate a) (x-coordinate b))
      (subtract reals (y-coordinate c) (y-coordinate b)))
    (multiply reals
      (subtract reals (y-coordinate a) (y-coordinate b))
      (subtract reals (x-coordinate c) (x-coordinate b)))
  == zero reals

record EuclideanPlane
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set₁ where

  field
    distance : Point R -> Point R -> R

    distance-nonnegative :
      (p q : Point R) ->
      lessOrEqual reals (zero reals) (distance p q)
    distance-self :
      (p : Point R) ->
      distance p p == zero reals
    distance-separates :
      (p q : Point R) ->
      distance p q == zero reals ->
      p == q
    distance-symmetric :
      (p q : Point R) ->
      distance p q == distance q p
    distance-triangle :
      (p q r : Point R) ->
      lessOrEqual reals
        (distance p r)
        (add reals (distance p q) (distance q r))
    distance-square :
      (p q : Point R) ->
      square reals (distance p q) ==
      SquaredDistance reals p q

open EuclideanPlane

module CevaStatement
  {R : Set}
  (reals : CompleteOrderedField R)
  (plane : EuclideanPlane reals) where

  proposition : Set
  proposition =
    (a b c d e f p : Point R) ->
    Not (Collinear reals a b c) ->
    Collinear reals b d c ->
    Collinear reals c e a ->
    Collinear reals a f b ->
    Collinear reals a p d ->
    Collinear reals b p e ->
    Collinear reals c p f ->
    multiply reals
      (multiply reals
        (distance plane b d)
        (distance plane c e))
      (distance plane a f)
    ==
    multiply reals
      (multiply reals
        (distance plane d c)
        (distance plane e a))
      (distance plane f b)

theorem-of-ceva : Set₁
theorem-of-ceva =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  (plane : EuclideanPlane reals) ->
  CevaStatement.proposition reals plane
