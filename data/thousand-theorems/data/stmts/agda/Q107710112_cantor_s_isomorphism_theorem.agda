-- Statement-only formalization of thousand-theorems corpus artifact Q107710112,
-- "Cantor's isomorphism theorem": any two countable, dense, nonempty linear
-- orders without endpoints are order isomorphic. This file contains no proof.

{-# OPTIONS --safe #-}

module Q107710112_cantor_s_isomorphism_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ)

infixr 4 _×_
infixr 3 _⊎_
infix 2 _↔_

data Bottom {a : Level} : Set a where

record Top {a : Level} : Set a where
  constructor truth

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

data _⊎_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → A ⊎ B
  right : B → A ⊎ B

record _↔_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor iff
  field
    forward  : A → B
    backward : B → A

Injective :
  {a b : Level} →
  {A : Set a} →
  {B : Set b} →
  (A → B) →
  Set (a ⊔ b)
Injective {A = A} function =
  (x y : A) →
  function x ≡ function y →
  x ≡ y

Countable :
  {a : Level} →
  Set a →
  Set a
Countable A =
  Σ (A → Nat) (λ code → Injective code)

Nonempty :
  {a : Level} →
  Set a →
  Set a
Nonempty {a} A =
  Σ A (λ _ → Top {a})

record LinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    less-than : A → A → Set a
    irreflexive :
      (x : A) →
      Not (less-than x x)
    transitive :
      (x y z : A) →
      less-than x y →
      less-than y z →
      less-than x z
    trichotomy :
      (x y : A) →
      less-than x y ⊎
      (x ≡ y ⊎ less-than y x)

Dense :
  {a : Level} →
  {A : Set a} →
  LinearOrder A →
  Set a
Dense {A = A} order =
  (x z : A) →
  LinearOrder.less-than order x z →
  Σ A
    (λ y →
      LinearOrder.less-than order x y ×
      LinearOrder.less-than order y z)

NoMinimum :
  {a : Level} →
  {A : Set a} →
  LinearOrder A →
  Set a
NoMinimum {A = A} order =
  (x : A) →
  Σ A (λ y → LinearOrder.less-than order y x)

NoMaximum :
  {a : Level} →
  {A : Set a} →
  LinearOrder A →
  Set a
NoMaximum {A = A} order =
  (x : A) →
  Σ A (λ y → LinearOrder.less-than order x y)

record OrderIsomorphism
  {a b : Level}
  {A : Set a}
  {B : Set b}
  (source : LinearOrder A)
  (target : LinearOrder B) :
  Set (a ⊔ b) where

  field
    to      : A → B
    from    : B → A
    from-to : (x : A) → from (to x) ≡ x
    to-from : (y : B) → to (from y) ≡ y
    order-equivalence :
      (x y : A) →
      LinearOrder.less-than source x y ↔
      LinearOrder.less-than target (to x) (to y)

cantor-isomorphism-theorem :
  {a b : Level} →
  Set (lsuc (a ⊔ b))
cantor-isomorphism-theorem {a} {b} =
  (A : Set a) →
  (B : Set b) →
  (orderA : LinearOrder A) →
  Countable A →
  Dense orderA →
  NoMinimum orderA →
  NoMaximum orderA →
  Nonempty A →
  (orderB : LinearOrder B) →
  Countable B →
  Dense orderB →
  NoMinimum orderB →
  NoMaximum orderB →
  Nonempty B →
  OrderIsomorphism orderA orderB
