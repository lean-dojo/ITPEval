-- Statement-only formalization of the Babel-formal topic supinf. This file contains no proof.

module supinf where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

data ⊥ : Set where

infixr 4 _∧_
infixr 3 _∨_
infix 2 _↔_

record _∧_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    left  : A
    right : B

data _∨_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    forward  : A → B
    backward : B → A

record CompleteOrderedField
  {ℓR ℓN : Level}
  (R : Set ℓR) (NatAlt : Set ℓN) :
  Set (lsuc (ℓR ⊔ ℓN)) where

  field
    zeroNat : NatAlt
    succ    : NatAlt → NatAlt
    natLe   : NatAlt → NatAlt → Set ℓN

    zero : R
    one  : R
    add  : R → R → R
    mul  : R → R → R
    opp  : R → R
    inv  : R → R
    rle  : R → R → Set ℓR
    rlt  : R → R → Set ℓR
    rabs : R → R
    inr  : NatAlt → R

    natLe-refl     : (n : NatAlt) → natLe n n
    le-succ-of-le  : (n m : NatAlt) → natLe n m → natLe n (succ m)
    le-succ        : (n : NatAlt) → natLe n (succ n)

    add-comm  : (x y : R) → add x y ≡ add y x
    add-assoc : (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero  : (x : R) → add x zero ≡ x
    add-opp   : (x : R) → add (opp x) x ≡ zero
    mul-comm  : (x y : R) → mul x y ≡ mul y x
    mul-assoc : (x y z : R) → mul (mul x y) z ≡ mul x (mul y z)
    mul-one   : (x : R) → mul x one ≡ x
    dist-left : (x y z : R) →
                mul x (add y z) ≡ add (mul x y) (mul x z)
    sub-zero  : (x : R) → add x (opp zero) ≡ x

    rle-refl    : (x : R) → rle x x
    rle-trans   : (x y z : R) → rle x y → rle y z → rle x z
    rle-antisym : (x y : R) → rle x y → rle y x → x ≡ y
    rlt-def     : (x y : R) →
                  rlt x y ↔ (rle x y ∧ (x ≡ y → ⊥))
    rle-abs     : (x : R) → rle (add x (opp zero)) (rabs x)
    inv-positive :
      (x : R) → rlt zero x → rlt zero (inv x)
    add-monotone-left :
      (x y z : R) → rle y z → rle (add x y) (add x z)
    inv-involutive :
      (x : R) → rlt zero x → inv (inv x) ≡ x

    inr-positive : (n : NatAlt) → rlt zero (inr (succ n))
    inr-le       : (m n : NatAlt) → natLe m n → rle (inr m) (inr n)
    inr-zero     : inr zeroNat ≡ zero
    inr-succ     : (n : NatAlt) → inr (succ n) ≡ add (inr n) one

    total-order :
      (x y : R) → rlt x y ∨ ((x ≡ y) ∨ rlt y x)
    inv-antitone :
      (a b : R) →
      rlt zero a →
      rlt zero b →
      rle a b →
      rle (inv b) (inv a)
    eps-between :
      (x y : R) →
      rlt x y →
      Σ R (λ eps → rlt zero eps ∧ rlt (add x eps) y)

    archimedean :
      (x : R) → Σ NatAlt (λ n → rle x (inr n))
    completeness :
      (A : R → Set ℓR) →
      Σ R (λ ub → (a : R) → A a → rle ub a) →
      Σ R (λ sup →
        ((a : R) → A a → rle a sup) ∧
        ((y : R) →
          ((a : R) → A a → rle a y) →
          rle sup y))

module SupInfStatements
  {ℓR ℓN : Level}
  {R : Set ℓR} {NatAlt : Set ℓN}
  (F : CompleteOrderedField R NatAlt) where

  open CompleteOrderedField F

  sub : R → R → R
  sub x y = add x (opp y)

  upBounds : (R → Set ℓR) → R → Set ℓR
  upBounds A x =
    (a : R) → A a → rle a x

  isMaximum : R → (R → Set ℓR) → Set ℓR
  isMaximum a A =
    A a ∧ upBounds A a

  lowBounds : (R → Set ℓR) → R → Set ℓR
  lowBounds A x =
    (a : R) → A a → rle x a

  isInf : R → (R → Set ℓR) → Set ℓR
  isInf x A =
    isMaximum x (lowBounds A)

  classic : Set (lsuc ℓR)
  classic =
    (P : Set ℓR) → P ∨ (P → ⊥)

  limit : (NatAlt → R) → R → Set (ℓR ⊔ ℓN)
  limit u l =
    (eps : R) →
    rlt zero eps →
    Σ NatAlt (λ cutoff →
      (n : NatAlt) →
      natLe cutoff n →
      rle (rabs (sub (u n) l)) eps)

  add-sub-cancel-r : Set ℓR
  add-sub-cancel-r =
    (a b : R) → add a (sub b a) ≡ b

  rabs-pos : Set ℓR
  rabs-pos =
    (t : R) → rle t (rabs t)

  unique-max : Set (lsuc ℓR)
  unique-max =
    (A : R → Set ℓR) (x y : R) →
    isMaximum x A →
    isMaximum y A →
    x ≡ y

  inf-lt : Set (lsuc ℓR)
  inf-lt =
    (A : R → Set ℓR) (x : R) →
    isInf x A →
    (y : R) →
    rlt x y →
    Σ R (λ a → A a ∧ rlt a y)

  le-of-le-add-eps : Set ℓR
  le-of-le-add-eps =
    (x y : R) →
    ((eps : R) → rlt zero eps → rle y (add x eps)) →
    rle y x

  le-lim : Set (ℓR ⊔ ℓN)
  le-lim =
    (x y : R) (u : NatAlt → R) →
    limit u x →
    ((n : NatAlt) → rle y (u n)) →
    rle y x

  inv-succ-pos : Set (ℓR ⊔ ℓN)
  inv-succ-pos =
    (n : NatAlt) → rlt zero (inv (inr (succ n)))

  limit-inv-succ : Set (ℓR ⊔ ℓN)
  limit-inv-succ =
    (eps : R) →
    rlt zero eps →
    Σ NatAlt (λ cutoff →
      (n : NatAlt) →
      natLe cutoff n →
      rle (inv (inr (succ n))) eps)
