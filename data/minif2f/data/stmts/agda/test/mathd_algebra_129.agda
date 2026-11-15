-- Statement-only formalization of miniF2F test problem mathd_algebra_129: a nonzero real
-- satisfying a reciprocal equation equals negative two. This file contains no proof.

module mathd-algebra-129 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
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

record RealFieldStructure (R : Set) : Set₁ where
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

record StandardReal
  {R : Set}
  (reals : RealFieldStructure R) : Set₁ where
  field
    archimedean :
      (x : R) →
      Exists Nat λ n →
        RealFieldStructure.lessOrEqual reals
          x
          (RealFieldStructure.fromNat reals n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          RealFieldStructure.lessOrEqual reals x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          RealFieldStructure.lessOrEqual reals x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            RealFieldStructure.lessOrEqual reals x upper) →
          RealFieldStructure.lessOrEqual reals supremum upper)

subtract :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
subtract reals x y =
  RealFieldStructure.add reals x
    (RealFieldStructure.negate reals y)

divide :
  {R : Set} →
  RealFieldStructure R →
  R →
  R →
  R
divide reals x y =
  RealFieldStructure.multiply reals x
    (RealFieldStructure.inverse reals y)

mathd-algebra-129 : Set₁
mathd-algebra-129 =
  (R : Set) →
  (reals : RealFieldStructure R) →
  StandardReal reals →
  (a : R) →
  a ≠ RealFieldStructure.zeroR reals →
  subtract reals
    (divide reals
      (RealFieldStructure.inverse reals
        (RealFieldStructure.fromNat reals 8))
      (RealFieldStructure.inverse reals
        (RealFieldStructure.fromNat reals 4)))
    (RealFieldStructure.inverse reals a)
    ≡ RealFieldStructure.oneR reals →
  a ≡ RealFieldStructure.negate reals
    (RealFieldStructure.fromNat reals 2)
