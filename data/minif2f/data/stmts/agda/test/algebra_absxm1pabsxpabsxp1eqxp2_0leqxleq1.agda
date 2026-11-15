-- Statement-only formalization of miniF2F test problem
-- algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1: a real number satisfying
-- |x - 1| + |x| + |x + 1| = x + 2 lies in [0, 1]. This file contains no proof.

module algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 where

open import Agda.Builtin.Equality using (_≡_)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists {A : Set} (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

record CompleteRealField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse absoluteValue : R → R
    lessOrEqual : R → R → Set

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    inverse-zero :
      inverse zeroR ≡ zeroR
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (inverse x) ≡ oneR

    order-reflexive :
      (x : R) → lessOrEqual x x
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-total :
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
    add-monotone :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)

    zero-less-or-equal-one :
      lessOrEqual zeroR oneR

    absolute-value-nonnegative :
      (x : R) → lessOrEqual zeroR (absoluteValue x)
    absolute-value-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-value-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

    least-upper-bound :
      (P : R → Set) →
      Exists P →
      Exists (λ upper →
        (x : R) → P x → lessOrEqual x upper) →
      Exists (λ supremum →
        ((x : R) → P x → lessOrEqual x supremum) ∧
        ((upper : R) →
          ((x : R) → P x → lessOrEqual x upper) →
          lessOrEqual supremum upper))

subtract : {R : Set} → CompleteRealField R → R → R → R
subtract reals x y =
  CompleteRealField.add reals x (CompleteRealField.negate reals y)

two : {R : Set} → CompleteRealField R → R
two reals =
  CompleteRealField.add reals
    (CompleteRealField.oneR reals)
    (CompleteRealField.oneR reals)

absoluteEquation : {R : Set} → CompleteRealField R → R → Set
absoluteEquation reals x =
  add
    (add
      (absoluteValue (subtract reals x oneR))
      (absoluteValue x))
    (absoluteValue (add x oneR))
  ≡ add x (two reals)
  where
    open CompleteRealField reals

inUnitInterval : {R : Set} → CompleteRealField R → R → Set
inUnitInterval reals x =
  CompleteRealField.lessOrEqual reals
    (CompleteRealField.zeroR reals) x
  ∧ CompleteRealField.lessOrEqual reals x
    (CompleteRealField.oneR reals)

algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 : Set₁
algebra_absxm1pabsxpabsxp1eqxp2_0leqxleq1 =
  (R : Set) →
  (reals : CompleteRealField R) →
  (x : R) →
  absoluteEquation reals x →
  inUnitInterval reals x
