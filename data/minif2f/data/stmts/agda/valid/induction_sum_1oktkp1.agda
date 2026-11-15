-- Statement-only formalization of miniF2F valid problem induction_sum_1oktkp1:
-- the sum from k = 0 through n - 1 of 1 / ((k + 1) * (k + 2)) equals
-- n / (n + 1). This file contains no proof.

module induction_sum_1oktkp1 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record RealFieldStructure (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

open RealFieldStructure

record StandardReal (R : Set) : Set₁ where
  field
    arithmetic : RealFieldStructure R
    lessOrEqual : R → R → Set

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
      lessOrEqual (add arithmetic z x) (add arithmetic z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual (zeroR arithmetic) x →
      lessOrEqual (zeroR arithmetic) y →
      lessOrEqual
        (zeroR arithmetic)
        (multiply arithmetic x y)
    zero-less-or-equal-one :
      lessOrEqual (zeroR arithmetic) (oneR arithmetic)

    archimedean :
      (x : R) →
      Exists Nat
        (λ n → lessOrEqual x (fromNat arithmetic n))

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            subset x →
            lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) →
              subset x →
              lessOrEqual x upper) →
            lessOrEqual supremum upper))

open StandardReal

sumFirst :
  {R : Set} →
  RealFieldStructure R →
  Nat →
  (Nat → R) →
  R
sumFirst reals zero term = zeroR reals
sumFirst reals (suc n) term =
  add reals (sumFirst reals n term) (term n)

divide :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
divide reals numerator denominator =
  multiply reals numerator (inverse reals denominator)

summand :
  {R : Set} →
  RealFieldStructure R →
  Nat →
  R
summand reals k =
  divide reals
    (oneR reals)
    (multiply reals
      (fromNat reals (suc k))
      (fromNat reals (suc (suc k))))

induction_sum_1oktkp1 : Set₁
induction_sum_1oktkp1 =
  (R : Set) →
  (standard : StandardReal R) →
  (n : Nat) →
  sumFirst (arithmetic standard) n
    (summand (arithmetic standard))
    ≡
  divide (arithmetic standard)
    (fromNat (arithmetic standard) n)
    (fromNat (arithmetic standard) (suc n))
