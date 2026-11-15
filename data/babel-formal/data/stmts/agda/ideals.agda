-- Statement-only formalization of the Babel-formal topic ideals. This file contains no proof.

module ideals where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _∧_

record _∧_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    left  : A
    right : B

record CRing {ℓ : Level} (R : Set ℓ) : Set ℓ where
  field
    zero : R
    one  : R
    add  : R → R → R
    mul  : R → R → R
    opp  : R → R

    add-comm  : (x y : R) → add x y ≡ add y x
    add-assoc : (x y z : R) →
                add (add x y) z ≡ add x (add y z)
    add-zero  : (x : R) → add x zero ≡ x
    add-opp   : (x : R) → add x (opp x) ≡ zero

    mul-comm  : (x y : R) → mul x y ≡ mul y x
    mul-assoc : (x y z : R) →
                mul (mul x y) z ≡ mul x (mul y z)
    mul-one   : (x : R) → mul x one ≡ x
    dist-left : (a x y : R) →
                mul a (add x y) ≡ add (mul a x) (mul a y)
    opp-add   : (x y : R) →
                opp (add x y) ≡ add (opp x) (opp y)

record IsIdeal
  {ℓ p : Level} {R : Set ℓ}
  (S : CRing R) (I : R → Set p) : Set (ℓ ⊔ p) where

  open CRing S

  field
    contains-zero : I zero
    closed-add    : (x y : R) → I x → I y → I (add x y)
    closed-opp    : (x : R) → I x → I (opp x)
    closed-mul    : (a x : R) → I x → I (mul a x)

Inter :
  ∀ {ℓ i p : Level} {R : Set ℓ} {A : Set i} →
  (A → R → Set p) → R → Set (i ⊔ p)
Inter {A = A} F x = (a : A) → F a x

IdealSum :
  ∀ {ℓ p : Level} {R : Set ℓ} →
  CRing R → (R → Set p) → (R → Set p) → R → Set (ℓ ⊔ p)
IdealSum {R = R} S I J x =
  Σ R (λ a →
    Σ R (λ b →
      I a ∧ (J b ∧ x ≡ CRing.add S a b)))

module IdealStatements
  {ℓ i p : Level} {R : Set ℓ}
  (S : CRing R) where

  inter-isIdeal :
    {A : Set i} →
    (F : A → R → Set p) →
    Set (ℓ ⊔ i ⊔ p)
  inter-isIdeal {A} F =
    ((a : A) → IsIdeal S (F a)) →
    IsIdeal S (Inter F)

  sum-isIdeal :
    (I J : R → Set p) →
    Set (ℓ ⊔ p)
  sum-isIdeal I J =
    IsIdeal S I →
    IsIdeal S J →
    IsIdeal S (IdealSum S I J)
