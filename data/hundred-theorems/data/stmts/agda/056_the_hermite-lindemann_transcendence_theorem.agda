-- Statement-only formalization of "The Hermite-Lindemann Transcendence Theorem" from
-- Hundred Theorems item 056: the complex exponential of every nonzero algebraic complex
-- number is transcendental. This file contains no proof.

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_ _≤_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

data _≤_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate reciprocal absoluteValue : R → R
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
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiply x (reciprocal x) ≡ oneR

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
      (x y : R) →
      lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ oneR ≠ zeroR

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
    characteristic-zero :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    absolute-nonnegative :
      (x : R) → lessOrEqual zeroR (absoluteValue x)
    absolute-of-nonnegative :
      (x : R) →
      lessOrEqual zeroR x →
      absoluteValue x ≡ x
    absolute-of-nonpositive :
      (x : R) →
      lessOrEqual x zeroR →
      absoluteValue x ≡ negate x

    archimedean :
      (x : R) → Σ Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set) →
      Σ R (λ x → P x) →
      Σ R (λ upper → (x : R) → P x → lessOrEqual x upper) →
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum) ∧
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

subtract :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  R
subtract reals x y =
  CompleteOrderedField.add reals x
    (CompleteOrderedField.negate reals y)

fromInt :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  R
fromInt reals (pos n) =
  CompleteOrderedField.fromNat reals n
fromInt reals (negsuc n) =
  CompleteOrderedField.negate reals
    (CompleteOrderedField.fromNat reals (suc n))

factorial : Nat → Nat
factorial zero = suc zero
factorial (suc n) = suc n * factorial n

StrictLess :
  {R : Set} →
  CompleteOrderedField R →
  R →
  R →
  Set
StrictLess reals x y =
  CompleteOrderedField.lessOrEqual reals x y ∧ x ≠ y

Positive :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Set
Positive reals x =
  StrictLess reals (CompleteOrderedField.zeroR reals) x

RealSequentialLimit :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → R) →
  R →
  Set
RealSequentialLimit {R} reals sequence limit =
  (epsilon : R) →
  Positive reals epsilon →
  Σ Nat
    (λ cutoff →
      (n : Nat) →
      cutoff ≤ n →
      CompleteOrderedField.lessOrEqual reals
        (CompleteOrderedField.absoluteValue reals
          (subtract reals (sequence n) limit))
        epsilon)

record Complex (R : Set) : Set where
  constructor complex
  field
    real      : R
    imaginary : R

complexZero :
  {R : Set} →
  CompleteOrderedField R →
  Complex R
complexZero reals =
  complex
    (CompleteOrderedField.zeroR reals)
    (CompleteOrderedField.zeroR reals)

complexOne :
  {R : Set} →
  CompleteOrderedField R →
  Complex R
complexOne reals =
  complex
    (CompleteOrderedField.oneR reals)
    (CompleteOrderedField.zeroR reals)

complexAdd :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexAdd reals (complex a b) (complex c d) =
  complex
    (CompleteOrderedField.add reals a c)
    (CompleteOrderedField.add reals b d)

complexMultiply :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Complex R
complexMultiply reals (complex a b) (complex c d) =
  complex
    (CompleteOrderedField.add reals
      (CompleteOrderedField.multiply reals a c)
      (CompleteOrderedField.negate reals
        (CompleteOrderedField.multiply reals b d)))
    (CompleteOrderedField.add reals
      (CompleteOrderedField.multiply reals a d)
      (CompleteOrderedField.multiply reals b c))

complexScale :
  {R : Set} →
  CompleteOrderedField R →
  R →
  Complex R →
  Complex R
complexScale reals scalar (complex a b) =
  complex
    (CompleteOrderedField.multiply reals scalar a)
    (CompleteOrderedField.multiply reals scalar b)

complexFromInt :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  Complex R
complexFromInt reals n =
  complex
    (fromInt reals n)
    (CompleteOrderedField.zeroR reals)

complexPower :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Nat →
  Complex R
complexPower reals z zero =
  complexOne reals
complexPower reals z (suc n) =
  complexMultiply reals z (complexPower reals z n)

complexPartialSum :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → Complex R) →
  Nat →
  Complex R
complexPartialSum reals sequence zero =
  complexZero reals
complexPartialSum reals sequence (suc n) =
  complexAdd reals
    (complexPartialSum reals sequence n)
    (sequence n)

ComplexSequentialLimit :
  {R : Set} →
  CompleteOrderedField R →
  (Nat → Complex R) →
  Complex R →
  Set
ComplexSequentialLimit reals sequence limit =
  RealSequentialLimit reals
    (λ n → Complex.real (sequence n))
    (Complex.real limit)
  ∧
  RealSequentialLimit reals
    (λ n → Complex.imaginary (sequence n))
    (Complex.imaginary limit)

exponentialTerm :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Nat →
  Complex R
exponentialTerm reals z n =
  complexScale reals
    (CompleteOrderedField.reciprocal reals
      (CompleteOrderedField.fromNat reals (factorial n)))
    (complexPower reals z n)

IsComplexExponential :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Complex R →
  Set
IsComplexExponential reals z exp-z =
  ComplexSequentialLimit reals
    (complexPartialSum reals (exponentialTerm reals z))
    exp-z

data HasNonzeroIntegerCoefficient : List Int → Set where
  here :
    {coefficient : Int} {coefficients : List Int} →
    coefficient ≠ pos zero →
    HasNonzeroIntegerCoefficient (coefficient ∷ coefficients)

  there :
    {coefficient : Int} {coefficients : List Int} →
    HasNonzeroIntegerCoefficient coefficients →
    HasNonzeroIntegerCoefficient (coefficient ∷ coefficients)

evaluateIntegerPolynomial :
  {R : Set} →
  CompleteOrderedField R →
  List Int →
  Complex R →
  Complex R
evaluateIntegerPolynomial reals [] z =
  complexZero reals
evaluateIntegerPolynomial reals
  (coefficient ∷ coefficients) z =
  complexAdd reals
    (complexFromInt reals coefficient)
    (complexMultiply reals z
      (evaluateIntegerPolynomial reals coefficients z))

Algebraic :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Set
Algebraic reals z =
  Σ (List Int)
    (λ coefficients →
      HasNonzeroIntegerCoefficient coefficients ∧
      evaluateIntegerPolynomial reals coefficients z ≡
      complexZero reals)

Transcendental :
  {R : Set} →
  CompleteOrderedField R →
  Complex R →
  Set
Transcendental reals z =
  ¬ Algebraic reals z

hundred-theorems-056 : Set₁
hundred-theorems-056 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  (x exp-x : Complex R) →
  x ≠ complexZero reals →
  Algebraic reals x →
  IsComplexExponential reals x exp-x →
  Transcendental reals exp-x
