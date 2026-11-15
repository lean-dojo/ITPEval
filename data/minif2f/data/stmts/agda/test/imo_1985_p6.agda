-- Statement-only formalization of miniF2F test problem imo_1985_p6. This file contains no
-- proof.

module imo-1985-p6 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat
  using (Nat; zero; suc)
  renaming (_+_ to _+N_; _*_ to _*N_)

infix 4 _≠_
infixr 4 _∧_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

record _∧_ (A B : Set) : Set where
  constructor conjunction
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

record ExistsUnique (A : Set) (P : A → Set) : Set where
  constructor uniqueWitness
  field
    value      : A
    property   : P value
    uniqueness : (other : A) → P other → other ≡ value

AtMost : {A : Set} → (A → A → Set) → A → A → Set
AtMost relation x y = relation x y ∨ x ≡ y

data PositiveNat : Nat → Set where
  positive : (n : Nat) → PositiveNat (suc n)

record StandardReal (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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
    fromNat-addition :
      (m n : Nat) →
      fromNat (m +N n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m *N n) ≡ multiply (fromNat m) (fromNat n)
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

module Statement {R : Set} (reals : StandardReal R) where
  open StandardReal reals

  infixl 6 _+_
  infixl 7 _*_ _/_
  infix 4 _<_

  _+_ : R → R → R
  _+_ = add

  _*_ : R → R → R
  _*_ = multiply

  _/_ : R → R → R
  x / y = x * inverse y

  _<_ : R → R → Set
  _<_ = lessThan

  proposition : Set
  proposition =
    (f : Nat → R → R) →
    ((x : R) →
      zeroR < x →
      f (suc zero) x ≡ x) →
    ((x : R) →
      zeroR < x →
      (n : Nat) →
      PositiveNat n →
      f (suc n) x ≡
        f n x * (f n x + oneR / fromNat n)) →
    ExistsUnique R λ a →
      (zeroR < a) ∧
      ((n : Nat) →
        PositiveNat n →
        (zeroR < f n a) ∧
        (f n a < f (suc n) a) ∧
        (f (suc n) a < oneR))

imo-1985-p6 : Set₁
imo-1985-p6 =
  (R : Set) →
  (reals : StandardReal R) →
  Statement.proposition reals
