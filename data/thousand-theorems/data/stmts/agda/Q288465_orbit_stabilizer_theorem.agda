-- Statement-only formalization of thousand-theorems corpus artifact Q288465,
-- "Orbit-stabilizer theorem": for a group acting on a type and a point, the
-- point's orbit is equivalent to the quotient by its stabilizer.
-- This file contains no proof.

module Q288465_orbit_stabilizer_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

record Group {ℓ : Level} (G : Set ℓ) : Set ℓ where
  field
    identity       : G
    inverse        : G → G
    multiply       : G → G → G
    associative    : (x y z : G) →
                     multiply x (multiply y z) ≡
                     multiply (multiply x y) z
    identity-left  : (x : G) → multiply identity x ≡ x
    identity-right : (x : G) → multiply x identity ≡ x
    inverse-left   : (x : G) → multiply (inverse x) x ≡ identity
    inverse-right  : (x : G) → multiply x (inverse x) ≡ identity

record Action
  {ℓG ℓX : Level}
  {G : Set ℓG}
  (group : Group G)
  (X : Set ℓX) :
  Set (ℓG ⊔ ℓX) where

  open Group group

  field
    act          : G → X → X
    act-identity : (x : X) → act identity x ≡ x
    act-multiply :
      (g h : G) →
      (x : X) →
      act (multiply g h) x ≡ act g (act h x)

record OrbitElement
  {ℓG ℓX : Level}
  {G : Set ℓG}
  {X : Set ℓX}
  {group : Group G}
  (action : Action group X)
  (point : X) :
  Set (ℓG ⊔ ℓX) where

  field
    value : X
    reachable :
      Σ G (λ g → Action.act action g point ≡ value)

OrbitEqual :
  {ℓG ℓX : Level} →
  {G : Set ℓG} →
  {X : Set ℓX} →
  {group : Group G} →
  (action : Action group X) →
  (point : X) →
  OrbitElement action point →
  OrbitElement action point →
  Set ℓX
OrbitEqual action point x y =
  OrbitElement.value x ≡ OrbitElement.value y

StabilizerQuotientRelated :
  {ℓG ℓX : Level} →
  {G : Set ℓG} →
  {X : Set ℓX} →
  (group : Group G) →
  (action : Action group X) →
  (point : X) →
  G →
  G →
  Set ℓX
StabilizerQuotientRelated group action point g h =
  Action.act action
    (Group.multiply group (Group.inverse group g) h)
    point
  ≡ point

record SetoidEquivalence
  {a b r s : Level}
  (A : Set a)
  (B : Set b)
  (_≈A_ : A → A → Set r)
  (_≈B_ : B → B → Set s) :
  Set (a ⊔ b ⊔ r ⊔ s) where

  field
    forward : A → B
    backward : B → A
    forward-congruent :
      (x y : A) →
      x ≈A y →
      forward x ≈B forward y
    backward-congruent :
      (x y : B) →
      x ≈B y →
      backward x ≈A backward y
    backward-forward :
      (x : A) →
      backward (forward x) ≈A x
    forward-backward :
      (y : B) →
      forward (backward y) ≈B y

orbit-stabilizer-theorem :
  (ℓG ℓX : Level) →
  Set (lsuc (ℓG ⊔ ℓX))
orbit-stabilizer-theorem ℓG ℓX =
  {G : Set ℓG} →
  {X : Set ℓX} →
  (group : Group G) →
  (action : Action group X) →
  (point : X) →
  SetoidEquivalence
    (OrbitElement action point)
    G
    (OrbitEqual action point)
    (StabilizerQuotientRelated group action point)
