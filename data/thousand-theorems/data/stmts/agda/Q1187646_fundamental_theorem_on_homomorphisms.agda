-- Statement-only formalization of thousand-theorems corpus artifact Q1187646,
-- "Fundamental theorem on homomorphisms": for every group homomorphism, the
-- quotient of its domain by its kernel is canonically isomorphic to its range.
-- This file contains no proof.

module Q1187646_fundamental_theorem_on_homomorphisms where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

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

record GroupHom
  {a b : Level}
  {G : Set a}
  {H : Set b}
  (domain : Group G)
  (codomain : Group H) :
  Set (a ⊔ b) where

  field
    map : G → H
    map-multiply :
      (x y : G) →
      map (Group.multiply domain x y) ≡
      Group.multiply codomain (map x) (map y)

record RestrictedMulEquiv
  {a b p q r s : Level}
  (A : Set a)
  (B : Set b)
  (domain-member : A → Set p)
  (codomain-member : B → Set q)
  (domain-related : A → A → Set r)
  (codomain-related : B → B → Set s)
  (domain-multiply : A → A → A)
  (codomain-multiply : B → B → B)
  (forward : A → B) :
  Set (a ⊔ b ⊔ p ⊔ q ⊔ r ⊔ s) where

  field
    inverse :
      (y : B) →
      codomain-member y →
      A
    forward-closed :
      (x : A) →
      domain-member x →
      codomain-member (forward x)
    inverse-closed :
      (y : B) →
      (hy : codomain-member y) →
      domain-member (inverse y hy)
    forward-congruent :
      (x y : A) →
      domain-member x →
      domain-member y →
      domain-related x y →
      codomain-related (forward x) (forward y)
    inverse-congruent :
      (x y : B) →
      (hx : codomain-member x) →
      (hy : codomain-member y) →
      codomain-related x y →
      domain-related (inverse x hx) (inverse y hy)
    map-multiply :
      (x y : A) →
      domain-member x →
      domain-member y →
      codomain-related
        (forward (domain-multiply x y))
        (codomain-multiply (forward x) (forward y))
    inverse-forward :
      (x : A) →
      (hx : domain-member x) →
      domain-related
        (inverse (forward x) (forward-closed x hx))
        x
    forward-inverse :
      (y : B) →
      (hy : codomain-member y) →
      codomain-related (forward (inverse y hy)) y

InRange :
  {a b : Level} →
  {G : Set a} →
  {H : Set b} →
  {domain : Group G} →
  {codomain : Group H} →
  GroupHom domain codomain →
  H →
  Set (a ⊔ b)
InRange {G = G} hom y =
  Σ G (λ x → GroupHom.map hom x ≡ y)

KernelQuotientRelated :
  {a b : Level} →
  {G : Set a} →
  {H : Set b} →
  {domain : Group G} →
  {codomain : Group H} →
  GroupHom domain codomain →
  G →
  G →
  Set b
KernelQuotientRelated {domain = domain} {codomain = codomain} hom x y =
  GroupHom.map hom
    (Group.multiply domain (Group.inverse domain x) y) ≡
  Group.identity codomain

-- Lean: QuotientGroup.quotientKerEquivRange
fundamental-theorem-on-homomorphisms :
  (a b : Level) →
  Set (lsuc (a ⊔ b))
fundamental-theorem-on-homomorphisms a b =
  {G : Set a} →
  {H : Set b} →
  (domain : Group G) →
  (codomain : Group H) →
  (hom : GroupHom domain codomain) →
  RestrictedMulEquiv
    G
    H
    (λ _ → ⊤ {a})
    (InRange hom)
    (KernelQuotientRelated hom)
    _≡_
    (Group.multiply domain)
    (Group.multiply codomain)
    (GroupHom.map hom)
