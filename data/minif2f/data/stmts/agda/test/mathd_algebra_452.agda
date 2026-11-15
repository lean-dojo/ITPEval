-- Statement-only formalization of miniF2F test problem mathd_algebra_452: a real-valued
-- sequence with constant first differences, a(1) = 2/3, and a(9) = 4/5 has
-- a(5) = 11/15. This file contains no proof.

module mathd-algebra-452 where

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

subtract : {R : Set} → OrderedField R → R → R → R
subtract reals x y =
  OrderedField.add reals x (OrderedField.negate reals y)

fraction : {R : Set} → OrderedField R → Nat → Nat → R
fraction reals numerator denominator =
  OrderedField.multiply reals
    (OrderedField.fromNat reals numerator)
    (OrderedField.inverse reals
      (OrderedField.fromNat reals denominator))

mathd-algebra-452 : Set₁
mathd-algebra-452 =
  (R : Set) →
  (standard : StandardReal R) →
  let reals = StandardReal.algebra standard
  in
  (a : Nat → R) →
  ((n : Nat) →
    subtract reals (a (n + 2)) (a (n + 1)) ≡
    subtract reals (a (n + 1)) (a n)) →
  a 1 ≡ fraction reals 2 3 →
  a 9 ≡ fraction reals 4 5 →
  a 5 ≡ fraction reals 11 15
