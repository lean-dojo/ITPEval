-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__080, "The Fundamental Theorem of Arithmetic": every positive
-- natural number has a unique nondecreasing list of prime factors whose product is the number.
-- This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _≤_ _∣_
infixr 5 _∷_
infixr 3 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤ : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : divisor * quotient ≡ dividend

data _∨_ (A B : Set) : Set where
  left : A → A ∨ B
  right : B → A ∨ B

record Prime (n : Nat) : Set where
  field
    at-least-two : 2 ≤ n
    divisor-is-trivial :
      (d : Nat) →
      d ∣ n →
      d ≡ 1 ∨ d ≡ n

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

data AllPrime : List Nat → Set where
  all-prime-empty : AllPrime []
  all-prime-cons :
    {p : Nat} {factors : List Nat} →
    Prime p →
    AllPrime factors →
    AllPrime (p ∷ factors)

data Sorted : List Nat → Set where
  sorted-empty : Sorted []
  sorted-singleton : {p : Nat} → Sorted (p ∷ [])
  sorted-cons :
    {p q : Nat} {factors : List Nat} →
    p ≤ q →
    Sorted (q ∷ factors) →
    Sorted (p ∷ q ∷ factors)

product : List Nat → Nat
product [] = 1
product (p ∷ factors) = p * product factors

record PrimeFactorization (n : Nat) (factors : List Nat) : Set where
  field
    factors-are-sorted : Sorted factors
    factors-are-prime : AllPrime factors
    product-is-number : product factors ≡ n

record ExistsUnique (A : Set) (P : A → Set) : Set where
  field
    value : A
    property : P value
    uniqueness : (other : A) → P other → other ≡ value

the-fundamental-theorem-of-arithmetic : Set
the-fundamental-theorem-of-arithmetic =
  (n : Nat) →
  1 ≤ n →
  ExistsUnique (List Nat) (PrimeFactorization n)
