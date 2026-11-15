-- Statement-only formalization of thousand-theorems corpus artifact Q179208,
-- "Cayley's theorem": every group with a faithful action on a type is
-- multiplicatively isomorphic to the image subgroup of its permutation action.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module Q179208_cayley_s_theorem where

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

record Permutation {ℓ : Level} (X : Set ℓ) : Set ℓ where
  field
    forward          : X → X
    backward         : X → X
    backward-forward : (x : X) → backward (forward x) ≡ x
    forward-backward : (x : X) → forward (backward x) ≡ x

infix 4 _≈ₚ_

_≈ₚ_ :
  {ℓ : Level} →
  {X : Set ℓ} →
  Permutation X →
  Permutation X →
  Set ℓ
p ≈ₚ q =
  (x : _) →
  Permutation.forward p x ≡ Permutation.forward q x

record FaithfulPermutationAction
  {ℓG ℓX : Level}
  {G : Set ℓG}
  (group : Group G)
  (X : Set ℓX) :
  Set (ℓG ⊔ ℓX) where

  open Group group

  field
    action : G → Permutation X
    action-identity :
      (x : X) →
      Permutation.forward (action identity) x ≡ x
    action-multiply :
      (g h : G) →
      (x : X) →
      Permutation.forward (action (multiply g h)) x ≡
      Permutation.forward (action g)
        (Permutation.forward (action h) x)
    faithful :
      (g h : G) →
      action g ≈ₚ action h →
      g ≡ h

record ActionImage
  {ℓG ℓX : Level}
  {G : Set ℓG}
  {X : Set ℓX}
  {group : Group G}
  (representation : FaithfulPermutationAction group X) :
  Set (ℓG ⊔ ℓX) where

  field
    permutation : Permutation X
    represented-by :
      Σ G
        (λ g →
          permutation ≈ₚ
          FaithfulPermutationAction.action representation g)

record MultiplicativeEquivalenceToImage
  {ℓG ℓX : Level}
  {G : Set ℓG}
  {X : Set ℓX}
  (group : Group G)
  (representation : FaithfulPermutationAction group X) :
  Set (ℓG ⊔ ℓX) where

  open Group group
  open ActionImage

  field
    to-image : G → ActionImage representation
    from-image : ActionImage representation → G
    from-respects-extensional-equality :
      (u v : ActionImage representation) →
      permutation u ≈ₚ permutation v →
      from-image u ≡ from-image v
    from-to :
      (g : G) →
      from-image (to-image g) ≡ g
    to-from :
      (u : ActionImage representation) →
      permutation (to-image (from-image u)) ≈ₚ permutation u
    preserves-identity :
      (x : X) →
      Permutation.forward (permutation (to-image identity)) x ≡ x
    preserves-multiplication :
      (g h : G) →
      (x : X) →
      Permutation.forward
        (permutation (to-image (multiply g h))) x ≡
      Permutation.forward (permutation (to-image g))
        (Permutation.forward (permutation (to-image h)) x)

cayleys-theorem :
  (ℓG ℓX : Level) →
  Set (lsuc (ℓG ⊔ ℓX))
cayleys-theorem ℓG ℓX =
  {G : Set ℓG} →
  {X : Set ℓX} →
  (group : Group G) →
  (representation : FaithfulPermutationAction group X) →
  MultiplicativeEquivalenceToImage group representation
