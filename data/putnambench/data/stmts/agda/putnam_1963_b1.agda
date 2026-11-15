-- Statement-only formalization of PutnamBench corpus artifact putnam_1963_b1:
-- the integer a for which x^2 - x + a divides x^13 + x + 90 over the real
-- numbers is exactly 2. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_

data Bottom : Set where

Not : Set → Set
Not A = A → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record Either (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Both (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Choice (A B : Set) : Set where
  choose-left  : A → Choice A B
  choose-right : B → Choice A B

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR inverseR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → addR x y ≡ addR y x
    add-associative :
      (x y z : R) → addR (addR x y) z ≡ addR x (addR y z)
    add-zero :
      (x : R) → addR x zeroR ≡ x
    add-inverse :
      (x : R) → addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡ multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) → multiplyR x oneR ≡ x
    multiply-zero :
      (x : R) → multiplyR x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    multiply-inverse :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (inverseR x) ≡ oneR

    order-reflexive :
      (x : R) → lessOrEqualR x x
    order-transitive :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-total :
      (x y : R) →
      Choice (lessOrEqualR x y) (lessOrEqualR y x)
    add-order :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-one :
      Both (lessOrEqualR zeroR oneR) (zeroR ≠ oneR)

    fromNat-zero :
      fromNatR zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNatR (suc n) ≡ addR (fromNatR n) oneR
    fromNat-addition :
      (m n : Nat) →
      fromNatR (m + n) ≡ addR (fromNatR m) (fromNatR n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNatR (m * n) ≡ multiplyR (fromNatR m) (fromNatR n)
    fromNat-injective :
      (m n : Nat) → fromNatR m ≡ fromNatR n → m ≡ n

    archimedean :
      (x : R) →
      Σ Nat (λ n → lessOrEqualR x (fromNatR n))
    least-upper-bound :
      (P : R → Set) →
      Σ R P →
      Σ R (λ upper → (x : R) → P x → lessOrEqualR x upper) →
      Σ R
        (λ supremum →
          Both
            ((x : R) → P x → lessOrEqualR x supremum)
            ((upper : R) →
              ((x : R) → P x → lessOrEqualR x upper) →
              lessOrEqualR supremum upper))

fromInt :
  {R : Set} →
  CompleteOrderedField R →
  Int →
  R
fromInt reals (pos n) =
  CompleteOrderedField.fromNatR reals n
fromInt reals (negsuc n) =
  CompleteOrderedField.negateR reals
    (CompleteOrderedField.fromNatR reals (suc n))

module PolynomialDefinitions
  {R : Set}
  (reals : CompleteOrderedField R) where

  open CompleteOrderedField reals

  Polynomial : Set
  Polynomial = List R

  coefficient : Polynomial → Nat → R
  coefficient [] n = zeroR
  coefficient (c ∷ coefficients) zero = c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  PolynomialEqual : Polynomial → Polynomial → Set
  PolynomialEqual p q =
    (n : Nat) → coefficient p n ≡ coefficient q n

  addPolynomial : Polynomial → Polynomial → Polynomial
  addPolynomial [] q = q
  addPolynomial p [] = p
  addPolynomial (a ∷ p) (b ∷ q) =
    addR a b ∷ addPolynomial p q

  negatePolynomial : Polynomial → Polynomial
  negatePolynomial [] = []
  negatePolynomial (a ∷ p) =
    negateR a ∷ negatePolynomial p

  subtractPolynomial : Polynomial → Polynomial → Polynomial
  subtractPolynomial p q =
    addPolynomial p (negatePolynomial q)

  scalePolynomial : R → Polynomial → Polynomial
  scalePolynomial c [] = []
  scalePolynomial c (a ∷ p) =
    multiplyR c a ∷ scalePolynomial c p

  multiplyPolynomial : Polynomial → Polynomial → Polynomial
  multiplyPolynomial [] q = []
  multiplyPolynomial (a ∷ p) q =
    addPolynomial
      (scalePolynomial a q)
      (zeroR ∷ multiplyPolynomial p q)

  onePolynomial : Polynomial
  onePolynomial = oneR ∷ []

  constantPolynomial : R → Polynomial
  constantPolynomial c = c ∷ []

  X : Polynomial
  X = zeroR ∷ oneR ∷ []

  powerPolynomial : Polynomial → Nat → Polynomial
  powerPolynomial p zero = onePolynomial
  powerPolynomial p (suc n) =
    multiplyPolynomial p (powerPolynomial p n)

  Divides : Polynomial → Polynomial → Set
  Divides divisor dividend =
    Σ Polynomial
      (λ quotient →
        PolynomialEqual dividend
          (multiplyPolynomial divisor quotient))

  quadratic : Int → Polynomial
  quadratic a =
    addPolynomial
      (subtractPolynomial (powerPolynomial X 2) X)
      (constantPolynomial (fromInt reals a))

  degree-thirteen-polynomial : Polynomial
  degree-thirteen-polynomial =
    addPolynomial
      (addPolynomial (powerPolynomial X 13) X)
      (constantPolynomial (fromNatR 90))

putnam-1963-b1 : Set₁
putnam-1963-b1 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  (a : Int) →
  Either
    (PolynomialDefinitions.Divides reals
      (PolynomialDefinitions.quadratic reals a)
      (PolynomialDefinitions.degree-thirteen-polynomial reals))
    (a ≡ pos 2)
