-- Statement-only formalization of miniF2F valid problem
-- numbertheory_aneqprodakp4_anmsqrtanp1eq2. This file contains no proof.

module numbertheory_aneqprodakp4_anmsqrtanp1eq2 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤ℕ_
infixr 3 _∨_

data ⊥ : Set where

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data _≤ℕ_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ℕ n
  suc≤suc : {m n : Nat} → m ≤ℕ n → suc m ≤ℕ suc n

record StandardRealSquareRoot (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate inverse squareRoot : R → R
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

    square-root-nonnegative :
      (x : R) → lessOrEqual zeroR (squareRoot x)
    square-root-square :
      (x : R) →
      lessOrEqual zeroR x →
      multiply (squareRoot x) (squareRoot x) ≡ x
    square-root-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      squareRoot x ≡ zeroR
    square-root-unique :
      (x y : R) →
      lessOrEqual zeroR y →
      multiply y y ≡ x →
      squareRoot x ≡ y

subtract :
  {R : Set} →
  StandardRealSquareRoot R →
  R →
  R →
  R
subtract reals x y =
  StandardRealSquareRoot.add reals
    x
    (StandardRealSquareRoot.negate reals y)

productInitial :
  {R : Set} →
  StandardRealSquareRoot R →
  (Nat → R) →
  Nat →
  R
productInitial reals a zero =
  StandardRealSquareRoot.oneR reals
productInitial reals a (suc n) =
  StandardRealSquareRoot.multiply reals
    (productInitial reals a n)
    (a n)

numbertheory_aneqprodakp4_anmsqrtanp1eq2 : Set₁
numbertheory_aneqprodakp4_anmsqrtanp1eq2 =
  (R : Set) →
  (reals : StandardRealSquareRoot R) →
  (a : Nat → R) →
  a zero ≡ StandardRealSquareRoot.oneR reals →
  ((n : Nat) →
    a (suc n) ≡
      StandardRealSquareRoot.add reals
        (productInitial reals a (suc n))
        (StandardRealSquareRoot.fromNat reals 4)) →
  (n : Nat) →
  suc zero ≤ℕ n →
  subtract reals
    (a n)
    (StandardRealSquareRoot.squareRoot reals (a (suc n)))
    ≡ StandardRealSquareRoot.fromNat reals 2
