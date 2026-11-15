-- Statement-only formalization of the Babel-formal topic polynomial. This file contains no
-- proof.

module polynomial where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _∧_
infixr 2 _∨_
infix 1 _↔_

data ⊥ : Set where

_≠_ : ∀ {a} {A : Set a} → A → A → Set a
x ≠ y = x ≡ y → ⊥

record _∧_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    first  : A
    second : B

data _∨_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A → A ∨ B
  right : B → A ∨ B

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    forward  : A → B
    backward : B → A

data MyNat : Set where
  zeroN : MyNat
  succN : MyNat → MyNat

mynat-add : MyNat → MyNat → MyNat
mynat-add zeroN     m = m
mynat-add (succN n) m = succN (mynat-add n m)

data MyNatLe : MyNat → MyNat → Set where
  le-refl : (n : MyNat) → MyNatLe n n
  le-step : {n m : MyNat} → MyNatLe n m → MyNatLe n (succN m)

mynat-add-zero-left : Set
mynat-add-zero-left =
  (m : MyNat) → mynat-add zeroN m ≡ m

mynat-add-succ-left : Set
mynat-add-succ-left =
  (n m : MyNat) →
  mynat-add (succN n) m ≡ succN (mynat-add n m)

mynat-zero-le : Set
mynat-zero-le =
  (n : MyNat) → MyNatLe zeroN n

mynat-add-zero-right : Set
mynat-add-zero-right =
  (n : MyNat) → mynat-add n zeroN ≡ n

mynat-succ-le-succ : Set
mynat-succ-le-succ =
  (n m : MyNat) →
  MyNatLe n m →
  MyNatLe (succN n) (succN m)

mynat-add-succ-right : Set
mynat-add-succ-right =
  (m n : MyNat) →
  mynat-add m (succN n) ≡ succN (mynat-add m n)

mynat-add-comm : Set
mynat-add-comm =
  (n m : MyNat) → mynat-add n m ≡ mynat-add m n

data MyList {a : Level} (A : Set a) : Set a where
  nilL  : MyList A
  consL : A → MyList A → MyList A

data InL {a : Level} {A : Set a} (x : A) : MyList A → Set a where
  in-head : {xs : MyList A} → InL x (consL x xs)
  in-tail : {y : A} {xs : MyList A} →
            InL x xs → InL x (consL y xs)

data NoDupL {a : Level} {A : Set a} : MyList A → Set a where
  nd-nil  : NoDupL nilL
  nd-cons : {x : A} {xs : MyList A} →
            (InL x xs → ⊥) →
            NoDupL xs →
            NoDupL (consL x xs)

lengthL : ∀ {a} {A : Set a} → MyList A → MyNat
lengthL nilL         = zeroN
lengthL (consL _ xs) = succN (lengthL xs)

record Ring {ℓ : Level} (A : Set ℓ) : Set ℓ where
  field
    zero : A
    opp  : A → A
    one  : A
    add  : A → A → A
    mul  : A → A → A

    one-neq-zero : one ≠ zero

    add-comm  : (x y : A) → add x y ≡ add y x
    add-assoc : (x y z : A) →
                add (add x y) z ≡ add x (add y z)
    add-zero  : (x : A) → add x zero ≡ x
    add-opp   : (x : A) → add x (opp x) ≡ zero

    mul-comm  : (x y : A) → mul x y ≡ mul y x
    mul-assoc : (x y z : A) →
                mul (mul x y) z ≡ mul x (mul y z)
    mul-one   : (x : A) → mul x one ≡ x
    dist-left : (x y z : A) →
                mul x (add y z) ≡ add (mul x y) (mul x z)
    mul-zero  : (x : A) → mul x zero ≡ zero

    no-zero-divisors :
      (x y : A) →
      mul x y ≡ zero →
      (x ≡ zero) ∨ (y ≡ zero)

module RingStatements
  {ℓ : Level} {A : Set ℓ}
  (structure : Ring A) where

  open Ring structure

  sub-eq-zero-left : Set ℓ
  sub-eq-zero-left =
    (a b : A) →
    add a (opp b) ≡ zero →
    a ≡ b

record PolynomialStructure
  {ℓR ℓP : Level} {R : Set ℓR} {P : Set ℓP}
  (base : Ring R) (poly : Ring P) : Set (ℓR ⊔ ℓP) where

  field
    degree   : P → MyNat
    monomial : MyNat → R → P
    eval     : P → R → R

    C-zero :
      monomial zeroN (Ring.zero base) ≡ Ring.zero poly
    C-one :
      monomial zeroN (Ring.one base) ≡ Ring.one poly
    deg-zero :
      degree (Ring.zero poly) ≡ zeroN

    eval-add :
      (p q : P) (x : R) →
      eval (Ring.add poly p q) x ≡
      Ring.add base (eval p x) (eval q x)
    eval-mul :
      (p q : P) (x : R) →
      eval (Ring.mul poly p q) x ≡
      Ring.mul base (eval p x) (eval q x)
    eval-C :
      (c x : R) →
      eval (monomial zeroN c) x ≡ c
    eval-X :
      (x : R) →
      eval (monomial (succN zeroN) (Ring.one base)) x ≡ x

    deg-C :
      (c : R) →
      c ≠ Ring.zero base →
      degree (monomial zeroN c) ≡ zeroN
    deg-constant :
      (p : P) →
      (degree p ≡ zeroN) ↔
      Σ R (λ c → p ≡ monomial zeroN c)
    deg-X-minus :
      (a : R) →
      degree
        (Ring.add poly
          (monomial (succN zeroN) (Ring.one base))
          (monomial zeroN (Ring.opp base a)))
      ≡ succN zeroN
    deg-mul :
      (p q : P) →
      p ≠ Ring.zero poly →
      q ≠ Ring.zero poly →
      degree (Ring.mul poly p q) ≡
      mynat-add (degree p) (degree q)

    euclid-X-minus :
      (p : P) (a : R) →
      Σ P (λ q →
        Σ P (λ r →
          (p ≡
            Ring.add poly
              (Ring.mul poly q
                (Ring.add poly
                  (monomial (succN zeroN) (Ring.one base))
                  (monomial zeroN (Ring.opp base a))))
              r)
          ∧ (degree r ≡ zeroN)))

module PolynomialStatements
  {ℓR ℓP : Level} {R : Set ℓR} {P : Set ℓP}
  (base : Ring R) (poly : Ring P)
  (structure : PolynomialStructure base poly) where

  open PolynomialStructure structure

  X : P
  X = monomial (succN zeroN) (Ring.one base)

  C : R → P
  C c = monomial zeroN c

  X-minus : R → P
  X-minus a =
    Ring.add poly X (C (Ring.opp base a))

  is-root : R → P → Set ℓR
  is-root a p = eval p a ≡ Ring.zero base

  poly-of-roots : MyList R → P
  poly-of-roots nilL =
    Ring.one poly
  poly-of-roots (consL a xs) =
    Ring.mul poly (X-minus a) (poly-of-roots xs)

  root-factor : Set (ℓR ⊔ ℓP)
  root-factor =
    (p : P) (a : R) →
    is-root a p →
    Σ P (λ q → p ≡ Ring.mul poly q (X-minus a))

  root-transfer : Set (ℓR ⊔ ℓP)
  root-transfer =
    (p q : P) (a b : R) →
    p ≡ Ring.mul poly q (X-minus a) →
    b ≠ a →
    is-root b p →
    is-root b q

  roots-le-degree : Set (ℓR ⊔ ℓP)
  roots-le-degree =
    (p : P) (xs : MyList R) →
    NoDupL xs →
    ((a : R) → InL a xs → is-root a p) →
    p ≠ Ring.zero poly →
    MyNatLe (lengthL xs) (degree p)

  X-minus-nonzero : Set (ℓR ⊔ ℓP)
  X-minus-nonzero =
    (a : R) → X-minus a ≠ Ring.zero poly

  constant-root-zero : Set (ℓR ⊔ ℓP)
  constant-root-zero =
    (p : P) (a : R) →
    degree p ≡ zeroN →
    is-root a p →
    p ≡ Ring.zero poly

  root-of-product : Set (ℓR ⊔ ℓP)
  root-of-product =
    (p q : P) (a : R) →
    is-root a (Ring.mul poly p q) →
    is-root a p ∨ is-root a q

  root-scale-constant : Set (ℓR ⊔ ℓP)
  root-scale-constant =
    (p : P) (c a : R) →
    c ≠ Ring.zero base →
    is-root a p ↔
    is-root a (Ring.mul poly (C c) p)

  poly-of-roots-nonzero : Set (ℓR ⊔ ℓP)
  poly-of-roots-nonzero =
    (xs : MyList R) →
    poly-of-roots xs ≠ Ring.zero poly

  deg-poly-of-roots : Set ℓR
  deg-poly-of-roots =
    (xs : MyList R) →
    degree (poly-of-roots xs) ≡ lengthL xs

  root-factor-list : Set (ℓR ⊔ ℓP)
  root-factor-list =
    (p : P) (xs : MyList R) →
    NoDupL xs →
    ((a : R) → InL a xs → is-root a p) →
    Σ P (λ q → p ≡ Ring.mul poly q (poly-of-roots xs))

  degree-factorisation : Set (ℓR ⊔ ℓP)
  degree-factorisation =
    (p : P) (xs : MyList R) (q : P) →
    p ≡ Ring.mul poly q (poly-of-roots xs) →
    q ≠ Ring.zero poly →
    degree p ≡ mynat-add (degree q) (lengthL xs)
