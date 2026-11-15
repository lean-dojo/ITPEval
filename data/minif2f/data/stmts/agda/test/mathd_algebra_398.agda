-- Statement-only formalization of miniF2F test problem mathd_algebra_398: positive real
-- numbers satisfying 9b = 20c and 7a = 4b also satisfy 63a = 80c. This file contains no proof.

module mathd-algebra-398 where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record OrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse : R → R
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

fromNat : {R : Set} → OrderedField R → Nat → R
fromNat reals zero = OrderedField.zeroR reals
fromNat reals (suc n) =
  OrderedField.add reals
    (fromNat reals n)
    (OrderedField.oneR reals)

-- Complete Archimedean ordered fields are unique up to ordered-field
-- isomorphism, so this structurally presents the standard real numbers.
record StandardReals (R : Set) : Set₁ where
  field
    algebra : OrderedField R

    archimedean :
      (x : R) →
      Exists Nat λ n →
        OrderedField.lessOrEqual algebra
          x
          (fromNat algebra n)

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

strictlyPositive : {R : Set} → OrderedField R → R → Set
strictlyPositive reals x =
  (OrderedField.lessOrEqual reals
    (OrderedField.zeroR reals) x) ∧
  (OrderedField.zeroR reals ≠ x)

statement : {R : Set} → OrderedField R → Set
statement {R} reals =
  (a b c : R) →
  (strictlyPositive reals a ∧
   strictlyPositive reals b ∧
   strictlyPositive reals c) →
  OrderedField.multiply reals (fromNat reals 9) b ≡
    OrderedField.multiply reals (fromNat reals 20) c →
  OrderedField.multiply reals (fromNat reals 7) a ≡
    OrderedField.multiply reals (fromNat reals 4) b →
  OrderedField.multiply reals (fromNat reals 63) a ≡
    OrderedField.multiply reals (fromNat reals 80) c

mathd-algebra-398 : Set₁
mathd-algebra-398 =
  (R : Set) →
  (reals : StandardReals R) →
  statement (StandardReals.algebra reals)
