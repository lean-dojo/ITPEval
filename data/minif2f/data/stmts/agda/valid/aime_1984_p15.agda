-- Statement-only formalization of miniF2F valid problem aime_1984_p15: four real variables
-- satisfying rational equations at parameters 2, 4, 6, and 8 have sum of squares 36. The real
-- numbers are represented by a complete Archimedean ordered field. This file contains no proof.

module aime-1984-p15 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

record RealNumberSystem (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
    lessOrEqual : R → R → Set
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
      (x y : R) →
      lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

square :
  {R : Set} →
  RealNumberSystem R →
  R →
  R
square reals x =
  RealNumberSystem.multiply reals x x

subtract :
  {R : Set} →
  RealNumberSystem R →
  R →
  R →
  R
subtract reals x y =
  RealNumberSystem.add reals x
    (RealNumberSystem.negate reals y)

divide :
  {R : Set} →
  RealNumberSystem R →
  R →
  R →
  R
divide reals x y =
  RealNumberSystem.multiply reals x
    (RealNumberSystem.inverse reals y)

sumFour :
  {R : Set} →
  RealNumberSystem R →
  R →
  R →
  R →
  R →
  R
sumFour reals a b c d =
  RealNumberSystem.add reals
    (RealNumberSystem.add reals
      (RealNumberSystem.add reals a b)
      c)
    d

denominator :
  {R : Set} →
  RealNumberSystem R →
  Nat →
  Nat →
  R
denominator reals parameter root =
  subtract reals
    (square reals (RealNumberSystem.fromNat reals parameter))
    (square reals (RealNumberSystem.fromNat reals root))

fractionTerm :
  {R : Set} →
  RealNumberSystem R →
  R →
  Nat →
  Nat →
  R
fractionTerm reals value parameter root =
  divide reals
    (square reals value)
    (denominator reals parameter root)

equation :
  {R : Set} →
  RealNumberSystem R →
  R →
  R →
  R →
  R →
  Nat →
  Set
equation reals x y z w parameter =
  sumFour reals
    (fractionTerm reals x parameter 1)
    (fractionTerm reals y parameter 3)
    (fractionTerm reals z parameter 5)
    (fractionTerm reals w parameter 7)
    ≡ RealNumberSystem.oneR reals

aime-1984-p15 : Set₁
aime-1984-p15 =
  (R : Set) →
  (reals : RealNumberSystem R) →
  (x y z w : R) →
  equation reals x y z w 2 →
  equation reals x y z w 4 →
  equation reals x y z w 6 →
  equation reals x y z w 8 →
  sumFour reals
    (square reals x)
    (square reals y)
    (square reals z)
    (square reals w)
    ≡ RealNumberSystem.fromNat reals 36
