-- Statement-only formalization of Hundred Theorems corpus artifact
-- hundred-theorems__agda__089, "The Factor and Remainder Theorems": for
-- polynomials over a commutative ring, division by X - a has remainder p(a),
-- and p(a) is zero exactly when X - a divides p. This file contains no proof.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _↔_
infixr 3 _×_

record _×_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor both
  field
    first : A
    second : B

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    forward : A → B
    backward : B → A

record CommutativeRing {r : Level} (R : Set r) : Set (lsuc r) where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR : R → R

    add-commutative :
      (x y : R) →
      addR x y ≡ addR y x
    add-associative :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zero :
      (x : R) →
      addR x zeroR ≡ x
    add-inverse :
      (x : R) →
      addR x (negateR x) ≡ zeroR

    multiply-commutative :
      (x y : R) →
      multiplyR x y ≡ multiplyR y x
    multiply-associative :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-one :
      (x : R) →
      multiplyR x oneR ≡ x
    distribute :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)

module PolynomialDefinitions
  {r : Level}
  {R : Set r}
  (ring : CommutativeRing R) where

  open CommutativeRing ring
  infix 4 _≈P_

  Polynomial : Set r
  Polynomial = List R

  coefficient : Polynomial → Nat → R
  coefficient [] n = zeroR
  coefficient (c ∷ coefficients) zero = c
  coefficient (c ∷ coefficients) (suc n) =
    coefficient coefficients n

  _≈P_ : Polynomial → Polynomial → Set r
  p ≈P q =
    (n : Nat) →
    coefficient p n ≡ coefficient q n

  constant : R → Polynomial
  constant c = c ∷ []

  indeterminate : Polynomial
  indeterminate = zeroR ∷ oneR ∷ []

  addPolynomial : Polynomial → Polynomial → Polynomial
  addPolynomial [] q = q
  addPolynomial p [] = p
  addPolynomial (a ∷ p) (b ∷ q) =
    addR a b ∷ addPolynomial p q

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

  evaluate : Polynomial → R → R
  evaluate [] x = zeroR
  evaluate (a ∷ p) x =
    addR a (multiplyR x (evaluate p x))

  linearFactor : R → Polynomial
  linearFactor a =
    negateR a ∷ oneR ∷ []

  DividesByLinear : R → Polynomial → Set r
  DividesByLinear a p =
    Σ Polynomial
      (λ q →
        p ≈P multiplyPolynomial (linearFactor a) q)

  RemainderDecomposition : Polynomial → R → Set r
  RemainderDecomposition p a =
    Σ Polynomial
      (λ q →
        p ≈P
          addPolynomial
            (multiplyPolynomial (linearFactor a) q)
            (constant (evaluate p a)))

  FactorAndRemainderStatement : Set r
  FactorAndRemainderStatement =
    ((p : Polynomial) →
      (a : R) →
      RemainderDecomposition p a)
    ×
    ((p : Polynomial) →
      (a : R) →
      (evaluate p a ≡ zeroR) ↔ DividesByLinear a p)

the-factor-and-remainder-theorems :
  {r : Level} →
  Set (lsuc r)
the-factor-and-remainder-theorems {r} =
  (R : Set r) →
  (ring : CommutativeRing R) →
  PolynomialDefinitions.FactorAndRemainderStatement ring
