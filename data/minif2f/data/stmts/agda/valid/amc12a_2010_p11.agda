-- Statement-only formalization of miniF2F valid problem amc12a_2010_p11:
-- a real exponential equation and logarithm condition determining a positive
-- logarithm base. This file contains no proof.

module amc12a-2010-p11 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor conjunction
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

AtMost : {A : Set} → (A → A → Set) → A → A → Set
AtMost relation x y = relation x y ∨ x ≡ y

-- Complete Archimedean ordered fields are categorical for the standard real
-- numbers. The order-compatible exponential and logarithm are inverse
-- operations up to a common positive scale, which cancels in real powers and
-- change-of-base logarithms.
record StandardReal (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse exponential logarithm : R → R
    lessThan : R → R → Set
    fromNat : Nat → R

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

    order-irreflexive :
      (x : R) → lessThan x x → ⊥
    order-transitive :
      (x y z : R) →
      lessThan x y →
      lessThan y z →
      lessThan x z
    order-trichotomy :
      (x y : R) →
      lessThan x y ∨ (x ≡ y ∨ lessThan y x)
    add-order :
      (x y z : R) →
      lessThan x y →
      lessThan (add z x) (add z y)
    multiply-positive :
      (x y : R) →
      lessThan zeroR x →
      lessThan zeroR y →
      lessThan zeroR (multiply x y)
    zero-less-than-one :
      lessThan zeroR oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-positive :
      (n : Nat) → lessThan zeroR (fromNat (suc n))

    archimedean :
      (x : R) →
      Exists Nat λ n →
        AtMost lessThan x (fromNat n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          AtMost lessThan x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          AtMost lessThan x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            AtMost lessThan x upper) →
          AtMost lessThan supremum upper)

    exponential-zero :
      exponential zeroR ≡ oneR
    exponential-add :
      (x y : R) →
      exponential (add x y) ≡
      multiply (exponential x) (exponential y)
    exponential-order :
      (x y : R) →
      lessThan x y →
      lessThan (exponential x) (exponential y)
    exponential-positive :
      (x : R) → lessThan zeroR (exponential x)
    logarithm-zero :
      logarithm zeroR ≡ zeroR
    logarithm-one :
      logarithm oneR ≡ zeroR
    exponential-logarithm :
      (x : R) →
      lessThan zeroR x →
      exponential (logarithm x) ≡ x
    logarithm-exponential :
      (x : R) → logarithm (exponential x) ≡ x

divide :
  {R : Set} →
  StandardReal R →
  R →
  R →
  R
divide reals x y =
  StandardReal.multiply reals x
    (StandardReal.inverse reals y)

realPower :
  {R : Set} →
  StandardReal R →
  R →
  R →
  R
realPower reals base exponent =
  StandardReal.exponential reals
    (StandardReal.multiply reals exponent
      (StandardReal.logarithm reals base))

naturalPower :
  {R : Set} →
  StandardReal R →
  R →
  Nat →
  R
naturalPower reals base zero =
  StandardReal.oneR reals
naturalPower reals base (suc exponent) =
  StandardReal.multiply reals
    (naturalPower reals base exponent)
    base

logBase :
  {R : Set} →
  StandardReal R →
  R →
  R →
  R
logBase reals base argument =
  divide reals
    (StandardReal.logarithm reals argument)
    (StandardReal.logarithm reals base)

amc12a-2010-p11 : Set₁
amc12a-2010-p11 =
  (R : Set) →
  (reals : StandardReal R) →
  (x b : R) →
  StandardReal.lessThan reals
    (StandardReal.zeroR reals)
    b →
  realPower reals
    (StandardReal.fromNat reals 7)
    (StandardReal.add reals
      x
      (StandardReal.fromNat reals 7))
    ≡
  realPower reals
    (StandardReal.fromNat reals 8)
    x →
  x ≡
    logBase reals
      b
      (naturalPower reals
        (StandardReal.fromNat reals 7)
        7) →
  b ≡
    divide reals
      (StandardReal.fromNat reals 8)
      (StandardReal.fromNat reals 7)
