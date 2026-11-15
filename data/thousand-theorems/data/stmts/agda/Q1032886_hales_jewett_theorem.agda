-- Statement-only formalization of thousand-theorems corpus artifact Q1032886,
-- "Hales–Jewett theorem": every finite coloring of sufficiently high-dimensional
-- words over a finite alphabet has a monochromatic combinatorial line.
-- This file contains no proof.

module Q1032886_hales_jewett_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

record Bijection
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y

FiniteType :
  {a : Level} →
  Set a →
  Set a
FiniteType A =
  Σ Nat (λ cardinality → Bijection A (Fin cardinality))

data Maybe
  {a : Level}
  (A : Set a) :
  Set a where

  nothing : Maybe A
  just    : A → Maybe A

record Line
  {a i : Level}
  (A : Set a)
  (I : Set i) :
  Set (a ⊔ i) where

  field
    index-word :
      I →
      Maybe A
    proper :
      Σ I (λ coordinate → index-word coordinate ≡ nothing)

open Line

line-point :
  {a i : Level} →
  {A : Set a} →
  {I : Set i} →
  Line A I →
  A →
  I →
  A
line-point line letter coordinate
  with index-word line coordinate
... | nothing = letter
... | just fixed-letter = fixed-letter

Monochromatic :
  {a i k : Level} →
  {A : Set a} →
  {I : Set i} →
  {K : Set k} →
  ((I → A) → K) →
  Line A I →
  Set (a ⊔ k)
Monochromatic {A = A} {K = K} coloring line =
  Σ K
    (λ color →
      (letter : A) →
      coloring (line-point line letter) ≡ color)

hales-jewett-theorem :
  {a k : Level} →
  Set (lsuc (a ⊔ k))
hales-jewett-theorem {a} {k} =
  (A : Set a) →
  FiniteType A →
  (K : Set k) →
  FiniteType K →
  Σ Set
    (λ I →
      FiniteType I
      ×
      ((coloring : (I → A) → K) →
        Σ (Line A I)
          (λ line → Monochromatic coloring line)))
