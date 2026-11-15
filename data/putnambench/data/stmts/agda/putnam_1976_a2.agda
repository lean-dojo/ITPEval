-- Statement-only formalization of PutnamBench corpus artifact putnam_1976_a2:
-- for every positive integer n, either (x+y)^n-x^n-y^n or
-- (x+y)^n+x^n+y^n is an integer polynomial in x^2y+xy^2 and x^2+xy+y^2.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

data Positive : Nat → Set where
  positive : {n : Nat} → Positive (suc n)

data Choice (A B : Set) : Set where
  choose-left  : A → Choice A B
  choose-right : B → Choice A B

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

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
    coefficient    : Int
    firstExponent  : Nat
    secondExponent : Nat

open Monomial

Polynomial : Set
Polynomial =
  List Monomial

coefficientAt : Polynomial → Nat → Nat → Int
coefficientAt [] i j =
  pos zero
coefficientAt (term ∷ terms) i j =
  addInt
    (ifInt
      (andBool
        (sameNat (firstExponent term) i)
        (sameNat (secondExponent term) j))
      (coefficient term)
      (pos zero))
    (coefficientAt terms i j)

PolynomialEqual : Polynomial → Polynomial → Set
PolynomialEqual p q =
  (i j : Nat) → coefficientAt p i j ≡ coefficientAt q i j

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
    (firstExponent term)
    (secondExponent term)
  ∷ negatePolynomial terms

subtractPolynomial : Polynomial → Polynomial → Polynomial
subtractPolynomial p q =
  appendPolynomial p (negatePolynomial q)

multiplyMonomial : Monomial → Monomial → Monomial
multiplyMonomial p q =
  monomial
    (multiplyInt (coefficient p) (coefficient q))
    (firstExponent p + firstExponent q)
    (secondExponent p + secondExponent q)

multiplyByMonomial : Monomial → Polynomial → Polynomial
multiplyByMonomial term [] =
  []
multiplyByMonomial term (factor ∷ factors) =
  multiplyMonomial term factor ∷ multiplyByMonomial term factors

multiplyPolynomial : Polynomial → Polynomial → Polynomial
multiplyPolynomial [] q =
  []
multiplyPolynomial (term ∷ terms) q =
  appendPolynomial
    (multiplyByMonomial term q)
    (multiplyPolynomial terms q)

constantPolynomial : Int → Polynomial
constantPolynomial c =
  monomial c zero zero ∷ []

onePolynomial : Polynomial
onePolynomial =
  constantPolynomial (pos one)

firstVariable : Polynomial
firstVariable =
  monomial (pos one) one zero ∷ []

secondVariable : Polynomial
secondVariable =
  monomial (pos one) zero one ∷ []

powerPolynomial : Polynomial → Nat → Polynomial
powerPolynomial p zero =
  onePolynomial
powerPolynomial p (suc n) =
  multiplyPolynomial p (powerPolynomial p n)

scalePolynomial : Int → Polynomial → Polynomial
scalePolynomial c [] =
  []
scalePolynomial c (term ∷ terms) =
  monomial
    (multiplyInt c (coefficient term))
    (firstExponent term)
    (secondExponent term)
  ∷ scalePolynomial c terms

substituteMonomial : Monomial → Polynomial → Polynomial → Polynomial
substituteMonomial term p q =
  scalePolynomial
    (coefficient term)
    (multiplyPolynomial
      (powerPolynomial p (firstExponent term))
      (powerPolynomial q (secondExponent term)))

substitute : Polynomial → Polynomial → Polynomial → Polynomial
substitute [] p q =
  []
substitute (term ∷ terms) p q =
  appendPolynomial
    (substituteMonomial term p q)
    (substitute terms p q)

P : Polynomial
P =
  appendPolynomial
    (multiplyPolynomial
      (powerPolynomial firstVariable two)
      secondVariable)
    (multiplyPolynomial
      firstVariable
      (powerPolynomial secondVariable two))

Q : Polynomial
Q =
  appendPolynomial
    (powerPolynomial firstVariable two)
    (appendPolynomial
      (multiplyPolynomial firstVariable secondVariable)
      (powerPolynomial secondVariable two))

F : Nat → Polynomial
F n =
  subtractPolynomial
    (subtractPolynomial
      (powerPolynomial
        (appendPolynomial firstVariable secondVariable)
        n)
      (powerPolynomial firstVariable n))
    (powerPolynomial secondVariable n)

G : Nat → Polynomial
G n =
  appendPolynomial
    (appendPolynomial
      (powerPolynomial
        (appendPolynomial firstVariable secondVariable)
        n)
      (powerPolynomial firstVariable n))
    (powerPolynomial secondVariable n)

putnam-1976-a2 : Set
putnam-1976-a2 =
  (n : Nat) →
  Positive n →
  Σ Polynomial
    (λ A →
      Choice
        (PolynomialEqual (F n) (substitute A P Q))
        (PolynomialEqual (G n) (substitute A P Q)))
