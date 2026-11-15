-- Statement-only formalization of "Desargues's Theorem" from Hundred Theorems
-- artifact hundred-theorems__agda__087: the projective ten-point collinearity
-- formulation and the affine parallel-side formulation. This file contains no proof.

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

record ProjectivePoint
  {R : Set}
  (reals : CompleteOrderedField R) :
  Set where

  constructor projective
  field
    x3 : R
    y3 : R
    z3 : R
    nonzero :
      Not
        (x3 == zero reals
         and y3 == zero reals
         and z3 == zero reals)

open ProjectivePoint

determinant3 :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ProjectivePoint reals ->
  ProjectivePoint reals ->
  ProjectivePoint reals ->
  R
determinant3 reals a b c =
  add reals
    (subtract reals
      (multiply reals
        (x3 a)
        (subtract reals
          (multiply reals (y3 b) (z3 c))
          (multiply reals (z3 b) (y3 c))))
      (multiply reals
        (y3 a)
        (subtract reals
          (multiply reals (x3 b) (z3 c))
          (multiply reals (z3 b) (x3 c)))))
    (multiply reals
      (z3 a)
      (subtract reals
        (multiply reals (x3 b) (y3 c))
        (multiply reals (y3 b) (x3 c))))

ProjectiveCollinear :
  {R : Set} ->
  (reals : CompleteOrderedField R) ->
  ProjectivePoint reals ->
  ProjectivePoint reals ->
  ProjectivePoint reals ->
  Set
ProjectiveCollinear reals a b c =
  determinant3 reals a b c == zero reals

record AffinePoint (R : Set) : Set where
  constructor affine
  field
    x2 : R
    y2 : R

open AffinePoint

AffineCollinear :
  {R : Set} ->
  CompleteOrderedField R ->
  AffinePoint R ->
  AffinePoint R ->
  AffinePoint R ->
  Set
AffineCollinear reals a b c =
  multiply reals
    (subtract reals (x2 b) (x2 a))
    (subtract reals (y2 c) (y2 a))
  ==
  multiply reals
    (subtract reals (y2 b) (y2 a))
    (subtract reals (x2 c) (x2 a))

ParallelLines :
  {R : Set} ->
  CompleteOrderedField R ->
  AffinePoint R ->
  AffinePoint R ->
  AffinePoint R ->
  AffinePoint R ->
  Set
ParallelLines reals a b c d =
  multiply reals
    (subtract reals (x2 b) (x2 a))
    (subtract reals (y2 d) (y2 c))
  ==
  multiply reals
    (subtract reals (y2 b) (y2 a))
    (subtract reals (x2 d) (x2 c))

module HolLightDirectStatement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (a aPrime b bPrime c cPrime p q r s :
      ProjectivePoint reals) ->
    Not (ProjectiveCollinear reals aPrime b s) ->
    Not (ProjectiveCollinear reals a p c) ->
    Not (ProjectiveCollinear reals a p r) ->
    Not (ProjectiveCollinear reals a c b) ->
    Not (ProjectiveCollinear reals a b r) ->
    Not (ProjectiveCollinear reals cPrime p aPrime) ->
    Not (ProjectiveCollinear reals cPrime p b) ->
    Not (ProjectiveCollinear reals cPrime p bPrime) ->
    Not (ProjectiveCollinear reals cPrime aPrime s) ->
    Not (ProjectiveCollinear reals cPrime aPrime bPrime) ->
    Not (ProjectiveCollinear reals p c aPrime) ->
    Not (ProjectiveCollinear reals p c b) ->
    Not (ProjectiveCollinear reals p aPrime r) ->
    Not (ProjectiveCollinear reals p b q) ->
    Not (ProjectiveCollinear reals p q bPrime) ->
    Not (ProjectiveCollinear reals c b s) ->
    Not (ProjectiveCollinear reals aPrime q bPrime) ->
    ProjectiveCollinear reals p aPrime a ->
    ProjectiveCollinear reals p b bPrime ->
    ProjectiveCollinear reals p cPrime c ->
    ProjectiveCollinear reals b c q ->
    ProjectiveCollinear reals bPrime cPrime q ->
    ProjectiveCollinear reals a r c ->
    ProjectiveCollinear reals aPrime cPrime r ->
    ProjectiveCollinear reals b s a ->
    ProjectiveCollinear reals aPrime s bPrime ->
    ProjectiveCollinear reals q s r

module RocqAffineStatement
  {R : Set}
  (reals : CompleteOrderedField R) where

  proposition : Set
  proposition =
    (a b c a1 b1 c1 s : AffinePoint R) ->
    c != c1 ->
    b != b1 ->
    c != s ->
    b != s ->
    c1 != s ->
    b1 != s ->
    a1 != b1 ->
    a1 != c1 ->
    b != c ->
    b1 != c1 ->
    Not (AffineCollinear reals a a1 b) ->
    Not (AffineCollinear reals a a1 c) ->
    AffineCollinear reals a a1 s ->
    AffineCollinear reals b b1 s ->
    AffineCollinear reals c c1 s ->
    ParallelLines reals a b a1 b1 ->
    ParallelLines reals a c a1 c1 ->
    ParallelLines reals b c b1 c1

hol-light-desargues-direct : Set1
hol-light-desargues-direct =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  HolLightDirectStatement.proposition reals

rocq-affine-desargues : Set1
rocq-affine-desargues =
  (R : Set) ->
  (reals : CompleteOrderedField R) ->
  RocqAffineStatement.proposition reals
