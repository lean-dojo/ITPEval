-- Statement-only formalization of miniF2F test problem induction_prod1p1onk3le3m1onn. This file
-- contains no proof.

module induction_prod1p1onk3le3m1onn where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infix 4 _≠_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data NatLess : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} → NatLess zero (suc n)
  successor-less-successor :
    {m n : Nat} → NatLess m n → NatLess (suc m) (suc n)

PositiveNat : Nat → Set
PositiveNat n = NatLess zero n

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

subtract : {R : Set} → RealStructure R → R → R → R
subtract reals x y =
  RealStructure.add reals x (RealStructure.negate reals y)

divide : {R : Set} → RealStructure R → R → R → R
divide reals x y =
  RealStructure.multiply reals x (RealStructure.inverse reals y)

power : {R : Set} → RealStructure R → R → Nat → R
power reals x zero =
  RealStructure.oneR reals
power reals x (suc n) =
  RealStructure.multiply reals x (power reals x n)

factor :
  {R : Set} →
  RealStructure R →
  Nat →
  R
factor reals k =
  RealStructure.add reals
    (RealStructure.oneR reals)
    (divide reals
      (RealStructure.oneR reals)
      (power reals (RealStructure.fromNat reals k) 3))

productOneTo :
  {R : Set} →
  RealStructure R →
  Nat →
  R
productOneTo reals zero =
  RealStructure.oneR reals
productOneTo reals (suc n) =
  RealStructure.multiply reals
    (productOneTo reals n)
    (factor reals (suc n))

induction_prod1p1onk3le3m1onn : Set₁
induction_prod1p1onk3le3m1onn =
  (R : Set) →
  (reals : RealStructure R) →
  (n : Nat) →
  PositiveNat n →
  RealStructure.lessOrEqual reals
    (productOneTo reals n)
    (subtract reals
      (RealStructure.fromNat reals 3)
      (divide reals
        (RealStructure.oneR reals)
        (RealStructure.fromNat reals n)))
