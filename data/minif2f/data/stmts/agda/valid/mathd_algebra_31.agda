-- Statement-only formalization of miniF2F valid problem mathd_algebra_31: a
-- nonnegative real sequence defined by a square-root recurrence and converging
-- to 9 has 9 as the corresponding fixed point. This file contains no proof.

module mathd-algebra-31 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤ℕ_
infixr 2 _∧_
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

data _≤ℕ_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ℕ n
  suc≤suc : {m n : Nat} → m ≤ℕ n → suc m ≤ℕ suc n

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

strictLess :
  {R : Set} →
  StandardRealSquareRoot R →
  R →
  R →
  Set
strictLess reals x y =
  StandardRealSquareRoot.lessOrEqual reals x y ∧ x ≠ y

nonnegative :
  {R : Set} →
  StandardRealSquareRoot R →
  R →
  Set
nonnegative reals x =
  StandardRealSquareRoot.lessOrEqual reals
    (StandardRealSquareRoot.zeroR reals)
    x

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

convergesTo :
  {R : Set} →
  StandardRealSquareRoot R →
  (Nat → R) →
  R →
  Set
convergesTo {R} reals u l =
  (ε : R) →
  strictLess reals
    (StandardRealSquareRoot.zeroR reals)
    ε →
  Exists Nat λ N →
    (n : Nat) →
    N ≤ℕ n →
    strictLess reals
      (subtract reals l ε)
      (u n)
    ∧
    strictLess reals
      (u n)
      (StandardRealSquareRoot.add reals l ε)

module Statement {R : Set} (reals : StandardRealSquareRoot R) where
  open StandardRealSquareRoot reals

  proposition : Set
  proposition =
    (x : R) →
    (u : Nat → R) →
    nonnegative reals x →
    ((n : Nat) → nonnegative reals (u n)) →
    ((n : Nat) →
      u (suc n) ≡ squareRoot (add x (u n))) →
    convergesTo reals u (fromNat 9) →
    fromNat 9 ≡ squareRoot (add x (fromNat 9))

mathd-algebra-31 : Set₁
mathd-algebra-31 =
  (R : Set) →
  (reals : StandardRealSquareRoot R) →
  Statement.proposition reals
