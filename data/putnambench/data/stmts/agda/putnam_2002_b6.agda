-- Statement-only formalization of PutnamBench corpus artifact putnam_2002_b6
-- (putnambench__agda__putnam_2002_b6): the determinant of the three-variable
-- Frobenius-power matrix modulo a prime is a finite product of integer linear
-- forms. This file contains no proof.

{-# OPTIONS --safe #-}

module Putnam2002B6 where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤_ _∣_
infixr 2 _∨_

data _≤_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

record _∣_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : dividend ≡ divisor * quotient

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

one : Nat
one = suc zero

two : Nat
two = suc one

record Prime (p : Nat) : Set where
  field
    at-least-two : two ≤ p
    only-trivial-divisors :
      (d : Nat) →
      d ∣ p →
      (d ≡ one) ∨ (d ≡ p)

negative : Nat → Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat → Nat → Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

negateInt : Int → Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

sameNat : Nat → Nat → Bool
sameNat zero zero =
  true
sameNat zero (suc n) =
  false
sameNat (suc m) zero =
  false
sameNat (suc m) (suc n) =
  sameNat m n

andBool : Bool → Bool → Bool
andBool true b =
  b
andBool false b =
  false

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false =
  when-true
ifInt false when-true when-false =
  when-false

record Monomial : Set where
  constructor monomial
  field
    coefficient : Int
    x-exponent  : Nat
    y-exponent  : Nat
    z-exponent  : Nat

open Monomial

Polynomial : Set
Polynomial =
  List Monomial

coefficientAt : Polynomial → Nat → Nat → Nat → Int
coefficientAt [] i j k =
  pos zero
coefficientAt (term ∷ terms) i j k =
  addInt
    (ifInt
      (andBool
        (sameNat (x-exponent term) i)
        (andBool
          (sameNat (y-exponent term) j)
          (sameNat (z-exponent term) k)))
      (coefficient term)
      (pos zero))
    (coefficientAt terms i j k)

appendPolynomial : Polynomial → Polynomial → Polynomial
appendPolynomial [] q =
  q
appendPolynomial (term ∷ terms) q =
  term ∷ appendPolynomial terms q

negatePolynomial : Polynomial → Polynomial
negatePolynomial [] =
  []
negatePolynomial (term ∷ terms) =
  monomial
    (negateInt (coefficient term))
    (x-exponent term)
    (y-exponent term)
    (z-exponent term)
  ∷ negatePolynomial terms

subtractPolynomial : Polynomial → Polynomial → Polynomial
subtractPolynomial p q =
  appendPolynomial p (negatePolynomial q)

multiplyMonomial : Monomial → Monomial → Monomial
multiplyMonomial p q =
  monomial
    (multiplyInt (coefficient p) (coefficient q))
    (x-exponent p + x-exponent q)
    (y-exponent p + y-exponent q)
    (z-exponent p + z-exponent q)

multiplyByMonomial : Monomial → Polynomial → Polynomial
multiplyByMonomial term [] =
  []
multiplyByMonomial term (factor ∷ factors) =
  multiplyMonomial term factor ∷
  multiplyByMonomial term factors

multiplyPolynomial : Polynomial → Polynomial → Polynomial
multiplyPolynomial [] q =
  []
multiplyPolynomial (term ∷ terms) q =
  appendPolynomial
    (multiplyByMonomial term q)
    (multiplyPolynomial terms q)

constantPolynomial : Int → Polynomial
constantPolynomial c =
  monomial c zero zero zero ∷ []

onePolynomial : Polynomial
onePolynomial =
  constantPolynomial (pos one)

scalePolynomial : Int → Polynomial → Polynomial
scalePolynomial c [] =
  []
scalePolynomial c (term ∷ terms) =
  monomial
    (multiplyInt c (coefficient term))
    (x-exponent term)
    (y-exponent term)
    (z-exponent term)
  ∷ scalePolynomial c terms

powerPolynomial : Polynomial → Nat → Polynomial
powerPolynomial p zero =
  onePolynomial
powerPolynomial p (suc n) =
  multiplyPolynomial p (powerPolynomial p n)

data Index3 : Set where
  first  : Index3
  second : Index3
  third  : Index3

variablePolynomial : Index3 → Polynomial
variablePolynomial first =
  monomial (pos one) one zero zero ∷ []
variablePolynomial second =
  monomial (pos one) zero one zero ∷ []
variablePolynomial third =
  monomial (pos one) zero zero one ∷ []

Matrix3 : Set
Matrix3 =
  Index3 → Index3 → Polynomial

putnamMatrix : Nat → Matrix3
putnamMatrix p first column =
  variablePolynomial column
putnamMatrix p second column =
  powerPolynomial (variablePolynomial column) p
putnamMatrix p third column =
  powerPolynomial (variablePolynomial column) (p * p)

determinant3 : Matrix3 → Polynomial
determinant3 M =
  appendPolynomial
    (subtractPolynomial
      (multiplyPolynomial
        (M first first)
        (multiplyPolynomial (M second second) (M third third)))
      (multiplyPolynomial
        (M first first)
        (multiplyPolynomial (M second third) (M third second))))
    (appendPolynomial
      (subtractPolynomial
        (multiplyPolynomial
          (M first second)
          (multiplyPolynomial (M second third) (M third first)))
        (multiplyPolynomial
          (M first second)
          (multiplyPolynomial (M second first) (M third third))))
      (subtractPolynomial
        (multiplyPolynomial
          (M first third)
          (multiplyPolynomial (M second first) (M third second)))
        (multiplyPolynomial
          (M first third)
          (multiplyPolynomial (M second second) (M third first)))))

record IntModEq (modulus : Nat) (left-value right-value : Int) : Set where
  field
    multiple : Int
    equation :
      left-value ≡
      addInt right-value (multiplyInt (pos modulus) multiple)

PolynomialCongruent : Nat → Polynomial → Polynomial → Set
PolynomialCongruent modulus f g =
  (i j k : Nat) →
  IntModEq modulus
    (coefficientAt f i j k)
    (coefficientAt g i j k)

record LinearCoefficients : Set where
  constructor coefficients
  field
    a : Int
    b : Int
    c : Int

open LinearCoefficients

linearForm : LinearCoefficients → Polynomial
linearForm values =
  appendPolynomial
    (scalePolynomial (a values) (variablePolynomial first))
    (appendPolynomial
      (scalePolynomial (b values) (variablePolynomial second))
      (scalePolynomial (c values) (variablePolynomial third)))

productOfLinearForms : List LinearCoefficients → Polynomial
productOfLinearForms [] =
  onePolynomial
productOfLinearForms (values ∷ rest) =
  multiplyPolynomial
    (linearForm values)
    (productOfLinearForms rest)

putnam-2002-b6 : Set
putnam-2002-b6 =
  (p : Nat) →
  Prime p →
  Exists (List LinearCoefficients)
    (λ factors →
      PolynomialCongruent p
        (determinant3 (putnamMatrix p))
        (productOfLinearForms factors))
