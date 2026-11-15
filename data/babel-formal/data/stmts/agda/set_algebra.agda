-- Statement-only formalization of the Babel-formal topic set_algebra. This file contains no
-- proof.

module set_algebra where

open import Agda.Primitive using (Level; lsuc; _⊔_)

infixr 2 _∨_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

data _∨_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

record _∧_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    first  : A
    second : B

record _↔_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    forward  : A → B
    backward : B → A

Not : ∀ {a : Level} → Set a → Set a
Not A = A → ⊥

ExcludedMiddle : (p : Level) → Set (lsuc p)
ExcludedMiddle p = (P : Set p) → P ∨ Not P

sUnion :
  ∀ {x p : Level} {X : Set x} →
  (X → Set p) → (X → Set p) → X → Set p
sUnion A B element = A element ∨ B element

sInter :
  ∀ {x p : Level} {X : Set x} →
  (X → Set p) → (X → Set p) → X → Set p
sInter A B element = A element ∧ B element

sCompl :
  ∀ {x p : Level} {X : Set x} →
  (X → Set p) → X → Set p
sCompl A element = Not (A element)

module SetAlgebraStatements
  {x p : Level} {X : Set x} where

  inter-distrib-left : Set (x ⊔ lsuc p)
  inter-distrib-left =
    ExcludedMiddle p →
    (A B C : X → Set p) →
    (element : X) →
    sInter A (sUnion B C) element ↔
    sUnion (sInter A B) (sInter A C) element

  inter-distrib-right : Set (x ⊔ lsuc p)
  inter-distrib-right =
    ExcludedMiddle p →
    (A B C : X → Set p) →
    (element : X) →
    sInter (sUnion A B) C element ↔
    sUnion (sInter A C) (sInter B C) element

  de-morgan-union : Set (x ⊔ lsuc p)
  de-morgan-union =
    ExcludedMiddle p →
    (A B : X → Set p) →
    (element : X) →
    sCompl (sUnion A B) element ↔
    sInter (sCompl A) (sCompl B) element

  de-morgan-inter : Set (x ⊔ lsuc p)
  de-morgan-inter =
    ExcludedMiddle p →
    (A B : X → Set p) →
    (element : X) →
    sCompl (sInter A B) element ↔
    sUnion (sCompl A) (sCompl B) element
