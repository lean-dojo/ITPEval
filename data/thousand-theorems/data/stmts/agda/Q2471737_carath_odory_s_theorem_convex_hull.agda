-- Statement-only formalization of thousand-theorems corpus artifact Q2471737,
-- "Carathéodory's theorem (convex hull)": over a linearly ordered field, the
-- convex hull of a set in a vector space is the union of the convex hulls of
-- its finite affine-independent subsets. This file contains no proof.

{-# OPTIONS --safe #-}

module Q2471737_carath_odory_s_theorem_convex_hull where

open import Agda.Primitive using (Level; _⊔_; lsuc; Setω)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _!=_
infixr 3 _and_
infixr 2 _or_

data Bottom : Set where

Not :
  {a : Level} ->
  Set a ->
  Set a
Not A =
  A -> Bottom

_!=_ :
  {a : Level} ->
  {A : Set a} ->
  A ->
  A ->
  Set a
x != y =
  Not (x == y)

record _and_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _or_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A -> A or B
  right : B -> A or B

record Exists
  {a b : Level}
  (A : Set a)
  (P : A -> Set b) :
  Set (a ⊔ b) where

  constructor witness
  field
    value    : A
    property : P value

record LogicalEquivalence
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor logically-equivalent
  field
    forward  : A -> B
    backward : B -> A

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

record LinearOrderedField
  {k : Level}
  (K : Set k) :
  Set (lsuc k) where

  field
    zeroK oneK : K
    addK multiplyK : K -> K -> K
    negateK inverseK : K -> K
    lessOrEqualK : K -> K -> Set k

    one-not-zero :
      oneK != zeroK

    add-commutative :
      (x y : K) ->
      addK x y == addK y x
    add-associative :
      (x y z : K) ->
      addK (addK x y) z == addK x (addK y z)
    add-zero :
      (x : K) ->
      addK x zeroK == x
    add-inverse :
      (x : K) ->
      addK x (negateK x) == zeroK

    multiply-commutative :
      (x y : K) ->
      multiplyK x y == multiplyK y x
    multiply-associative :
      (x y z : K) ->
      multiplyK (multiplyK x y) z ==
      multiplyK x (multiplyK y z)
    multiply-one :
      (x : K) ->
      multiplyK x oneK == x
    multiply-zero :
      (x : K) ->
      multiplyK x zeroK == zeroK
    distribute :
      (x y z : K) ->
      multiplyK x (addK y z) ==
      addK (multiplyK x y) (multiplyK x z)
    inverse-zero :
      inverseK zeroK == zeroK
    multiply-inverse :
      (x : K) ->
      x != zeroK ->
      multiplyK x (inverseK x) == oneK

    order-reflexive :
      (x : K) ->
      lessOrEqualK x x
    order-transitive :
      (x y z : K) ->
      lessOrEqualK x y ->
      lessOrEqualK y z ->
      lessOrEqualK x z
    order-antisymmetric :
      (x y : K) ->
      lessOrEqualK x y ->
      lessOrEqualK y x ->
      x == y
    order-total :
      (x y : K) ->
      (lessOrEqualK x y) or (lessOrEqualK y x)
    add-order :
      (x y z : K) ->
      lessOrEqualK x y ->
      lessOrEqualK (addK z x) (addK z y)
    multiply-nonnegative :
      (x y : K) ->
      lessOrEqualK zeroK x ->
      lessOrEqualK zeroK y ->
      lessOrEqualK zeroK (multiplyK x y)
    zero-less-than-one :
      (lessOrEqualK zeroK oneK) and (zeroK != oneK)

open LinearOrderedField

record VectorSpace
  {k e : Level}
  {K : Set k}
  (orderedField : LinearOrderedField K)
  (E : Set e) :
  Set (lsuc (k ⊔ e)) where

  field
    zeroE : E
    addE : E -> E -> E
    negateE : E -> E
    scaleE : K -> E -> E

    add-commutativeE :
      (x y : E) ->
      addE x y == addE y x
    add-associativeE :
      (x y z : E) ->
      addE (addE x y) z == addE x (addE y z)
    add-zeroE :
      (x : E) ->
      addE x zeroE == x
    add-inverseE :
      (x : E) ->
      addE x (negateE x) == zeroE

    scale-one :
      (x : E) ->
      scaleE (oneK orderedField) x == x
    scale-associative :
      (a b : K) ->
      (x : E) ->
      scaleE (multiplyK orderedField a b) x ==
      scaleE a (scaleE b x)
    scale-add-vectors :
      (a : K) ->
      (x y : E) ->
      scaleE a (addE x y) ==
      addE (scaleE a x) (scaleE a y)
    scale-add-scalars :
      (a b : K) ->
      (x : E) ->
      scaleE (addK orderedField a b) x ==
      addE (scaleE a x) (scaleE b x)
    scale-zero-vector :
      (a : K) ->
      scaleE a zeroE == zeroE
    scale-zero-scalar :
      (x : E) ->
      scaleE (zeroK orderedField) x == zeroE

open VectorSpace

sumScalars :
  {k : Level}
  {K : Set k} ->
  (orderedField : LinearOrderedField K) ->
  {n : Nat} ->
  (Fin n -> K) ->
  K
sumScalars orderedField {zero} coefficients =
  zeroK orderedField
sumScalars orderedField {suc n} coefficients =
  addK orderedField
    (coefficients fzero)
    (sumScalars orderedField (\ i -> coefficients (fsuc i)))

sumScaled :
  {k e : Level}
  {K : Set k}
  {E : Set e}
  {orderedField : LinearOrderedField K} ->
  (space : VectorSpace orderedField E) ->
  {n : Nat} ->
  (Fin n -> K) ->
  (Fin n -> E) ->
  E
sumScaled space {zero} coefficients points =
  zeroE space
sumScaled space {suc n} coefficients points =
  addE space
    (scaleE space (coefficients fzero) (points fzero))
    (sumScaled space
      (\ i -> coefficients (fsuc i))
      (\ i -> points (fsuc i)))

Injective :
  {a b : Level}
  {A : Set a}
  {B : Set b} ->
  (A -> B) ->
  Set (a ⊔ b)
Injective f =
  (x y : _) ->
  f x == f y ->
  x == y

AffineIndependent :
  {k e : Level}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  (space : VectorSpace orderedField E) ->
  {n : Nat} ->
  (Fin n -> E) ->
  Set (k ⊔ e)
AffineIndependent {K = K} orderedField space {n} points =
  (coefficients : Fin n -> K) ->
  sumScalars orderedField coefficients == zeroK orderedField ->
  sumScaled space coefficients points == zeroE space ->
  (i : Fin n) ->
  coefficients i == zeroK orderedField

ConvexCombination :
  {k e : Level}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  (space : VectorSpace orderedField E) ->
  {n : Nat} ->
  (Fin n -> E) ->
  E ->
  Set (k ⊔ e)
ConvexCombination {K = K} orderedField space {n} points x =
  Exists (Fin n -> K)
    (\ coefficients ->
      ((i : Fin n) ->
        lessOrEqualK orderedField
          (zeroK orderedField)
          (coefficients i))
      and
      ((sumScalars orderedField coefficients == oneK orderedField)
      and
      (sumScaled space coefficients points == x)))

ConvexHull :
  {k e p : Level}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  (space : VectorSpace orderedField E) ->
  (E -> Set p) ->
  E ->
  Set (k ⊔ e ⊔ p)
ConvexHull {E = E} orderedField space subset x =
  Exists Nat
    (\ n ->
      Exists (Fin n -> E)
        (\ points ->
          ((i : Fin n) -> subset (points i))
          and
          ConvexCombination orderedField space points x))

FiniteIndependentHull :
  {k e p : Level}
  {K : Set k}
  {E : Set e} ->
  (orderedField : LinearOrderedField K) ->
  (space : VectorSpace orderedField E) ->
  (E -> Set p) ->
  E ->
  Set (k ⊔ e ⊔ p)
FiniteIndependentHull {E = E} orderedField space subset x =
  Exists Nat
    (\ n ->
      Exists (Fin n -> E)
        (\ points ->
          Injective points
          and
          (((i : Fin n) -> subset (points i))
          and
          (AffineIndependent orderedField space points
          and
          ConvexCombination orderedField space points x))))

SameSubset :
  {e p q : Level}
  {E : Set e} ->
  (E -> Set p) ->
  (E -> Set q) ->
  Set (e ⊔ p ⊔ q)
SameSubset {E = E} lhs rhs =
  (x : E) ->
  LogicalEquivalence (lhs x) (rhs x)

caratheodory-convex-hull : Setω
caratheodory-convex-hull =
  {k e p : Level} ->
  (K : Set k) ->
  (orderedField : LinearOrderedField K) ->
  (E : Set e) ->
  (space : VectorSpace orderedField E) ->
  (subset : E -> Set p) ->
  SameSubset
    (ConvexHull orderedField space subset)
    (FiniteIndependentHull orderedField space subset)
