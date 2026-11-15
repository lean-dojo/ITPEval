-- Statement-only formalization of PutnamBench corpus artifact putnam_1986_b3:
-- integer-polynomial factorization modulo a prime lifts compatibly to every
-- positive prime power under a Bezout congruence. This file contains no proof.

{-# OPTIONS --safe #-}

open import Agda.Builtin.Equality renaming (_≡_ to _==_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<=N_ _dividesN_ _dividesZ_
infixr 8 _^N_
infixr 3 _and_
infixr 2 _or_

record _and_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A -> Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Positive : Nat -> Set where
  positive : {n : Nat} -> Positive (suc n)

data _<=N_ : Nat -> Nat -> Set where
  zero<=N   : {n : Nat} -> zero <=N n
  suc<=sucN : {m n : Nat} -> m <=N n -> suc m <=N suc n

record _dividesN_ (divisor dividend : Nat) : Set where
  field
    quotient : Nat
    equation : dividend == divisor * quotient

data _or_ (A B : Set) : Set where
  left  : A -> A or B
  right : B -> A or B

record Prime (p : Nat) : Set where
  field
    at-least-two :
      suc (suc zero) <=N p
    only-trivial-divisors :
      (d : Nat) ->
      d dividesN p ->
      (d == suc zero) or (d == p)

oneN : Nat
oneN =
  suc zero

_^N_ : Nat -> Nat -> Nat
base ^N zero =
  oneN
base ^N (suc exponent) =
  (base ^N exponent) * base

negative : Nat -> Int
negative zero =
  pos zero
negative (suc n) =
  negsuc n

difference : Nat -> Nat -> Int
difference zero zero =
  pos zero
difference (suc m) zero =
  pos (suc m)
difference zero (suc n) =
  negsuc n
difference (suc m) (suc n) =
  difference m n

addInt : Int -> Int -> Int
addInt (pos m) (pos n) =
  pos (m + n)
addInt (pos m) (negsuc n) =
  difference m (suc n)
addInt (negsuc m) (pos n) =
  difference n (suc m)
addInt (negsuc m) (negsuc n) =
  negsuc (suc (m + n))

negateInt : Int -> Int
negateInt (pos n) =
  negative n
negateInt (negsuc n) =
  pos (suc n)

multiplyInt : Int -> Int -> Int
multiplyInt (pos m) (pos n) =
  pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

record _dividesZ_ (divisor dividend : Int) : Set where
  field
    integer-quotient : Int
    integer-equation :
      dividend == multiplyInt divisor integer-quotient

Polynomial : Set
Polynomial =
  List Int

coefficientAt : Polynomial -> Nat -> Int
coefficientAt [] index =
  pos zero
coefficientAt (coefficient ∷ coefficients) zero =
  coefficient
coefficientAt (coefficient ∷ coefficients) (suc index) =
  coefficientAt coefficients index

addPolynomial : Polynomial -> Polynomial -> Polynomial
addPolynomial [] q =
  q
addPolynomial p [] =
  p
addPolynomial (coefficientP ∷ coefficientsP)
              (coefficientQ ∷ coefficientsQ) =
  addInt coefficientP coefficientQ
  ∷ addPolynomial coefficientsP coefficientsQ

negatePolynomial : Polynomial -> Polynomial
negatePolynomial [] =
  []
negatePolynomial (coefficient ∷ coefficients) =
  negateInt coefficient ∷ negatePolynomial coefficients

subtractPolynomial : Polynomial -> Polynomial -> Polynomial
subtractPolynomial p q =
  addPolynomial p (negatePolynomial q)

scalePolynomial : Int -> Polynomial -> Polynomial
scalePolynomial scalar [] =
  []
scalePolynomial scalar (coefficient ∷ coefficients) =
  multiplyInt scalar coefficient
  ∷ scalePolynomial scalar coefficients

shiftPolynomial : Polynomial -> Polynomial
shiftPolynomial coefficients =
  pos zero ∷ coefficients

multiplyPolynomial : Polynomial -> Polynomial -> Polynomial
multiplyPolynomial [] q =
  []
multiplyPolynomial (coefficient ∷ coefficients) q =
  addPolynomial
    (scalePolynomial coefficient q)
    (shiftPolynomial (multiplyPolynomial coefficients q))

onePolynomial : Polynomial
onePolynomial =
  pos oneN ∷ []

Congruent : Polynomial -> Polynomial -> Nat -> Set
Congruent f g modulus =
  (index : Nat) ->
  pos modulus dividesZ
    coefficientAt (subtractPolynomial f g) index

putnam-1986-b3 : Set
putnam-1986-b3 =
  (n p : Nat) ->
  Positive n ->
  Positive p ->
  Prime p ->
  (f g h r s : Polynomial) ->
  Congruent
    (addPolynomial
      (multiplyPolynomial r f)
      (multiplyPolynomial s g))
    onePolynomial
    p ->
  Congruent (multiplyPolynomial f g) h p ->
  Exists Polynomial
    (\ F ->
      Exists Polynomial
        (\ G ->
          Congruent F f p
          and
          Congruent G g p
          and
          Congruent
            (multiplyPolynomial F G)
            h
            (p ^N n)))
