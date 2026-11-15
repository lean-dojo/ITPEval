-- Statement-only formalization of PutnamBench corpus artifact putnam_1992_b2
-- (putnambench__agda__putnam_1992_b2): the coefficient of x^k in
-- (1 + x + x^2 + x^3)^n equals the stated finite binomial sum.
-- This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_; _*_)

one : Nat
one =
  suc zero

two : Nat
two =
  suc one

choose : Nat -> Nat -> Nat
choose n zero =
  one
choose zero (suc k) =
  zero
choose (suc n) (suc k) =
  choose n (suc k) + choose n k

lessOrEqual : Nat -> Nat -> Bool
lessOrEqual zero n =
  true
lessOrEqual (suc m) zero =
  false
lessOrEqual (suc m) (suc n) =
  lessOrEqual m n

ifNat : Bool -> Nat -> Nat -> Nat
ifNat true when-true when-false =
  when-true
ifNat false when-true when-false =
  when-false

sumThrough : Nat -> (Nat -> Nat) -> Nat
sumThrough zero term =
  term zero
sumThrough (suc n) term =
  sumThrough n term + term (suc n)

Polynomial : Set
Polynomial =
  List Nat

coefficient : Polynomial -> Nat -> Nat
coefficient [] k =
  zero
coefficient (a ∷ coefficients) zero =
  a
coefficient (a ∷ coefficients) (suc k) =
  coefficient coefficients k

addPolynomial : Polynomial -> Polynomial -> Polynomial
addPolynomial [] q =
  q
addPolynomial p [] =
  p
addPolynomial (a ∷ p) (b ∷ q) =
  (a + b) ∷ addPolynomial p q

scalePolynomial : Nat -> Polynomial -> Polynomial
scalePolynomial scalar [] =
  []
scalePolynomial scalar (a ∷ p) =
  (scalar * a) ∷ scalePolynomial scalar p

multiplyPolynomial : Polynomial -> Polynomial -> Polynomial
multiplyPolynomial [] q =
  []
multiplyPolynomial (a ∷ p) q =
  addPolynomial
    (scalePolynomial a q)
    (zero ∷ multiplyPolynomial p q)

onePolynomial : Polynomial
onePolynomial =
  one ∷ []

powerPolynomial : Polynomial -> Nat -> Polynomial
powerPolynomial p zero =
  onePolynomial
powerPolynomial p (suc n) =
  multiplyPolynomial p (powerPolynomial p n)

basePolynomial : Polynomial
basePolynomial =
  one ∷ one ∷ one ∷ one ∷ []

Q : Nat -> Nat -> Nat
Q n k =
  coefficient (powerPolynomial basePolynomial n) k

binomialSummand : Nat -> Nat -> Nat -> Nat
binomialSummand n k j =
  choose n j
  *
  ifNat
    (lessOrEqual (two * j) k)
    (choose n (k - two * j))
    zero

putnam-1992-b2 : Set
putnam-1992-b2 =
  (n k : Nat) ->
  Q n k == sumThrough k (binomialSummand n k)
