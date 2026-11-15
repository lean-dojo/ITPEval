-- Statement-only formalization of miniF2F valid artifact aime_1988_p4: a lower
-- bound on the length of a real sequence from an absolute-value sum identity.
-- This file contains no proof.

module aime-1988-p4 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤N_ _≈Q_ _≉Q_ _≤Q_ _<Q_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor _,_
  field
    left  : A
    right : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _≤N_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤N n
  suc≤suc : {m n : Nat} → m ≤N n → suc m ≤N suc n

-- A rational is (positivePart - negativePart) / (denominatorMinusOne + 1).
-- Equality and order below quotient the non-canonical representations.
record Rat : Set where
  constructor fraction
  field
    positivePart       : Nat
    negativePart       : Nat
    denominatorMinusOne : Nat

_≈Q_ : Rat → Rat → Set
fraction p n d ≈Q fraction q m e =
  p * suc e + m * suc d ≡ q * suc d + n * suc e

_≤Q_ : Rat → Rat → Set
fraction p n d ≤Q fraction q m e =
  p * suc e + m * suc d ≤N q * suc d + n * suc e

_≉Q_ : Rat → Rat → Set
x ≉Q y = x ≈Q y → ⊥

_<Q_ : Rat → Rat → Set
x <Q y = x ≤Q y ∧ x ≉Q y

zeroQ : Rat
zeroQ = fraction zero zero zero

fromNatQ : Nat → Rat
fromNatQ n = fraction n zero zero

negateQ : Rat → Rat
negateQ (fraction p n d) = fraction n p d

addQ : Rat → Rat → Rat
addQ (fraction p n d) (fraction q m e) =
  fraction
    (p * suc e + q * suc d)
    (n * suc e + m * suc d)
    (d + e + d * e)

Cut : Set₁
Cut = Rat → Set

CutEqual : Cut → Cut → Set
CutEqual P Q = (r : Rat) → P r ↔ Q r

CutLessOrEqual : Cut → Cut → Set
CutLessOrEqual P Q = (r : Rat) → P r → Q r

CutLess : Cut → Cut → Set
CutLess P Q =
  Exists Rat
    (λ separator →
      (P separator → ⊥) ∧
      Q separator)

-- Located, rounded, proper lower cuts are a concrete presentation of the
-- standard real numbers; CutEqual is their extensional equality.
record IsDedekindReal (P : Cut) : Set₁ where
  field
    respects-rational-equality :
      (p q : Rat) → p ≈Q q → P p → P q
    inhabited :
      Exists Rat P
    proper :
      Exists Rat (λ q → P q → ⊥)
    downward-closed :
      (p q : Rat) → p <Q q → P q → P p
    rounded :
      (p : Rat) →
      P p →
      Exists Rat (λ q → p <Q q ∧ P q)
    located :
      (p q : Rat) →
      p <Q q →
      P p ∨ (P q → ⊥)

fromNatCut : Nat → Cut
fromNatCut n q = q <Q fromNatQ n

addCut : Cut → Cut → Cut
addCut P Q r =
  Exists Rat
    (λ p →
      Exists Rat
        (λ q →
          P p ∧
          (Q q ∧ r <Q addQ p q)))

negateCut : Cut → Cut
negateCut P q =
  Exists Rat
    (λ r →
      (P r → ⊥) ∧
      q <Q negateQ r)

absoluteValueCut : Cut → Cut
absoluteValueCut P q =
  P q ∨ negateCut P q

sumFirst : Nat → (Nat → Cut) → Cut
sumFirst zero term =
  fromNatCut zero
sumFirst (suc n) term =
  addCut (sumFirst n term) (term n)

aime-1988-p4 : Set₁
aime-1988-p4 =
  (n : Nat) →
  (a : Nat → Cut) →
  ((k : Nat) → IsDedekindReal (a k)) →
  ((k : Nat) →
    CutLess
      (absoluteValueCut (a k))
      (fromNatCut 1)) →
  CutEqual
    (sumFirst n (λ k → absoluteValueCut (a k)))
    (addCut
      (fromNatCut 19)
      (absoluteValueCut (sumFirst n a))) →
  20 ≤N n
