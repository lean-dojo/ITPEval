-- Statement-only formalization of miniF2F test problem amc12a_2020_p10: over the standard real
-- numbers, a nested logarithm equation implies that the decimal digits of n sum to 13.
-- This file contains no proof.

module amc12a-2020-p10 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper; mod-helper)

infix 4 _≠_
infixr 3 _∨_
infixr 2 _∧_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} → NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

AtMost : {A : Set} → (A → A → Set) → A → A → Set
AtMost relation x y = relation x y ∨ x ≡ y

-- Complete Archimedean ordered fields are categorical for the standard real
-- numbers. The exponential and logarithm laws below select the usual
-- order-compatible inverse operations, up to the harmless common scale that
-- cancels in every change-of-base quotient.
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
    inverse-positive :
      (x : R) →
      lessThan zeroR x →
      lessThan zeroR (inverse x)

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
    fromNat-above-one :
      (n : Nat) →
      NatLess 1 n →
      lessThan oneR (fromNat n)

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
    logarithm-order :
      (x y : R) →
      lessThan zeroR x →
      lessThan x y →
      lessThan (logarithm x) (logarithm y)
    logarithm-positive-above-one :
      (x : R) →
      lessThan oneR x →
      lessThan zeroR (logarithm x)
    exponential-logarithm :
      (x : R) →
      lessThan zeroR x →
      exponential (logarithm x) ≡ x
    logarithm-exponential :
      (x : R) → logarithm (exponential x) ≡ x

    natural-log-base-positive :
      (base argument : Nat) →
      NatLess 1 base →
      NatLess 1 argument →
      lessThan zeroR
        (multiply
          (logarithm (fromNat argument))
          (inverse (logarithm (fromNat base))))

divide :
  {R : Set} →
  StandardReal R →
  R →
  R →
  R
divide reals x y =
  StandardReal.multiply reals x
    (StandardReal.inverse reals y)

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

naturalDiv : Nat → Nat → Nat
naturalDiv numerator zero = zero
naturalDiv numerator (suc denominator) =
  div-helper zero denominator numerator denominator

naturalMod : Nat → Nat → Nat
naturalMod numerator zero = zero
naturalMod numerator (suc denominator) =
  mod-helper zero denominator numerator denominator

sumDigitsAux : Nat → Nat → Nat
sumDigitsAux zero n = zero
sumDigitsAux (suc fuel) zero = zero
sumDigitsAux (suc fuel) (suc n) =
  naturalMod (suc n) 10 +
  sumDigitsAux fuel (naturalDiv (suc n) 10)

sumDigits : Nat → Nat
sumDigits n = sumDigitsAux (suc n) n

amc12a-2020-p10 : Set₁
amc12a-2020-p10 =
  (R : Set) →
  (reals : StandardReal R) →
  (n : Nat) →
  NatLess 1 n →
  logBase reals
    (StandardReal.fromNat reals 2)
    (logBase reals
      (StandardReal.fromNat reals 16)
      (StandardReal.fromNat reals n))
  ≡
  logBase reals
    (StandardReal.fromNat reals 4)
    (logBase reals
      (StandardReal.fromNat reals 4)
      (StandardReal.fromNat reals n)) →
  sumDigits n ≡ 13
