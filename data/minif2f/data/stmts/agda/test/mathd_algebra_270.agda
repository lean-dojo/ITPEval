-- Statement-only formalization of miniF2F test problem mathd_algebra_270:
-- a real function equal to 1 / (x + 2) away from -2 satisfies
-- f (f 1) = 3 / 7. This file contains no proof.

module mathd-algebra-270 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

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

record RealStructure (R : Set) : Set₁ where
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

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

-- Completeness and the Archimedean property characterize the real-number
-- domain up to ordered-field isomorphism.
record StandardRealStructure (R : Set) : Set₁ where
  field
    algebra : RealStructure R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealStructure.lessOrEqual algebra
          x
          (RealStructure.fromNat algebra n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealStructure.lessOrEqual algebra x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealStructure.lessOrEqual algebra x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealStructure.lessOrEqual algebra x upper) →
          RealStructure.lessOrEqual algebra supremum upper)

divide :
  {R : Set} →
  RealStructure R →
  R →
  R →
  R
divide reals x y =
  RealStructure.multiply reals x
    (RealStructure.inverse reals y)

mathd-algebra-270 : Set₁
mathd-algebra-270 =
  (R : Set) →
  (standard : StandardRealStructure R) →
  let reals = StandardRealStructure.algebra standard
  in
  (f : R → R) →
  ((x : R) →
    x ≠ RealStructure.negate reals
      (RealStructure.fromNat reals 2) →
    f x ≡ divide reals
      (RealStructure.oneR reals)
      (RealStructure.add reals x
        (RealStructure.fromNat reals 2))) →
  f (f (RealStructure.fromNat reals 1)) ≡
    divide reals
      (RealStructure.fromNat reals 3)
      (RealStructure.fromNat reals 7)
