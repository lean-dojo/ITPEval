-- Statement-only formalization of PutnamBench corpus artifact putnam_1968_a5:
-- the sharp maximum of the absolute derivative at zero among real quadratic
-- polynomials bounded in absolute value by one on [0, 1] is eight. This file
-- contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

record QuadraticPolynomial (R : Set) : Set where
  constructor quadratic
  field
    leadingCoefficient : R
    linearCoefficient  : R
    constantCoefficient : R

open QuadraticPolynomial

evaluate :
  {R : Set} ->
  CompleteOrderedField R ->
  QuadraticPolynomial R ->
  R ->
  R
evaluate reals polynomial x =
  add reals
    (add reals
      (multiply reals
        (leadingCoefficient polynomial)
        (multiply reals x x))
      (multiply reals
        (linearCoefficient polynomial)
        x))
    (constantCoefficient polynomial)

InUnitInterval :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  Set
InUnitInterval reals x =
  lessOrEqual reals (zeroR reals) x
  and
  lessOrEqual reals x (oneR reals)

BoundedBy :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
BoundedBy reals bound value =
  lessOrEqual reals (negate reals bound) value
  and
  lessOrEqual reals value bound

QualifyingQuadratic :
  {R : Set} ->
  CompleteOrderedField R ->
  QuadraticPolynomial R ->
  Set
QualifyingQuadratic {R} reals polynomial =
  leadingCoefficient polynomial != zeroR reals
  and
  ((x : R) ->
    InUnitInterval reals x ->
    BoundedBy reals
      (oneR reals)
      (evaluate reals polynomial x))

AbsoluteValueEquals :
  {R : Set} ->
  CompleteOrderedField R ->
  R ->
  R ->
  Set
AbsoluteValueEquals reals value magnitude =
  value == magnitude
  or
  value == negate reals magnitude

record SharpDerivativeMaximum
  {R : Set}
  (reals : CompleteOrderedField R)
  (maximum : R) : Set where
  field
    maximizingPolynomial : QuadraticPolynomial R
    maximizingPolynomial-qualifies :
      QualifyingQuadratic reals maximizingPolynomial
    maximum-is-attained :
      AbsoluteValueEquals reals
        (linearCoefficient maximizingPolynomial)
        maximum
    universal-upper-bound :
      (polynomial : QuadraticPolynomial R) ->
      QualifyingQuadratic reals polynomial ->
      BoundedBy reals maximum
        (linearCoefficient polynomial)

putnam-1968-a5 : Set1
putnam-1968-a5 =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  SharpDerivativeMaximum reals (fromNat reals 8)
