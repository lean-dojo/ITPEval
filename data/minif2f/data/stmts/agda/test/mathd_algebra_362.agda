-- Statement-only formalization of miniF2F test problem mathd_algebra_362: over the real
-- numbers, a^2 * b^3 = 32/27 and a/(b^3) = 27/4 imply a + b = 8/3. This file
-- contains no proof.

module mathd-algebra-362 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

record OrderedField (R : Set) : Set₁ where
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
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)
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
    fromNat-addition :
      (m n : Nat) →
      fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n
    fromNat-nonnegative :
      (n : Nat) → lessOrEqual zeroR (fromNat n)

-- Complete Archimedean ordered fields present the standard real numbers,
-- uniquely up to ordered-field isomorphism.
record StandardReal (R : Set) : Set₁ where
  field
    algebra : OrderedField R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        OrderedField.lessOrEqual algebra
          x
          (OrderedField.fromNat algebra n)

    least-upper-bound :
      (subset : R → Set) →
      Exists R subset →
      Exists R
        (λ upper →
          (x : R) →
          subset x →
          OrderedField.lessOrEqual algebra x upper) →
      Exists R λ supremum →
        ((x : R) →
          subset x →
          OrderedField.lessOrEqual algebra x supremum) ∧
        ((upper : R) →
          ((x : R) →
            subset x →
            OrderedField.lessOrEqual algebra x upper) →
          OrderedField.lessOrEqual algebra supremum upper)

divide : {R : Set} → OrderedField R → R → R → R
divide reals x y =
  OrderedField.multiply reals x (OrderedField.inverse reals y)

power : {R : Set} → OrderedField R → R → Nat → R
power reals x zero = OrderedField.oneR reals
power reals x (suc n) =
  OrderedField.multiply reals x (power reals x n)

mathd-algebra-362 : Set₁
mathd-algebra-362 =
  (R : Set) →
  (standard : StandardReal R) →
  let reals = StandardReal.algebra standard
  in
  (a b : R) →
  OrderedField.multiply reals
    (power reals a 2)
    (power reals b 3)
    ≡ divide reals
        (OrderedField.fromNat reals 32)
        (OrderedField.fromNat reals 27) →
  divide reals a (power reals b 3)
    ≡ divide reals
        (OrderedField.fromNat reals 27)
        (OrderedField.fromNat reals 4) →
  OrderedField.add reals a b
    ≡ divide reals
        (OrderedField.fromNat reals 8)
        (OrderedField.fromNat reals 3)
