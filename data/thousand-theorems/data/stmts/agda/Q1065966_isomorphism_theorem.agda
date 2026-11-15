-- Statement-only formalization of thousand-theorems corpus artifact Q1065966,
-- "Isomorphism theorem": the canonical first, second, and third isomorphisms
-- for groups and their quotient groups. This file contains no proof.

module Q1065966_isomorphism_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _⊆_
infixr 5 _×_

data ⊤ {ℓ : Level} : Set ℓ where
  tt : ⊤

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor _,_
  field
    first  : A
    second : B

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

record SubgroupOf
  {ℓ : Level}
  {G : Set ℓ}
  (structure : Group G) :
  Set (lsuc ℓ) where

  field
    member : G → Set ℓ
    membership-propositional :
      (x : G) (u v : member x) → u ≡ v
    contains-identity :
      member (Group.identity structure)
    closed-under-inverse :
      (x : G) →
      member x →
      member (Group.inverse structure x)
    closed-under-multiply :
      (x y : G) →
      member x →
      member y →
      member (Group.multiply structure x y)

_⊆_ :
  {ℓ : Level} →
  {G : Set ℓ} →
  {structure : Group G} →
  SubgroupOf structure →
  SubgroupOf structure →
  Set ℓ
H ⊆ K =
  (x : _) →
  SubgroupOf.member H x →
  SubgroupOf.member K x

record Normal
  {ℓ : Level}
  {G : Set ℓ}
  {structure : Group G}
  (N : SubgroupOf structure) :
  Set ℓ where

  field
    closed-under-conjugation :
      (g n : G) →
      SubgroupOf.member N n →
      SubgroupOf.member N
        (Group.multiply structure
          (Group.multiply structure g n)
          (Group.inverse structure g))

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

QuotientRelated :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  G →
  G →
  Set ℓ
QuotientRelated structure N x y =
  SubgroupOf.member N
    (Group.multiply structure (Group.inverse structure x) y)

ProductMember :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  SubgroupOf structure →
  G →
  Set ℓ
ProductMember {G = G} structure H N x =
  Σ G (λ h →
    SubgroupOf.member H h ×
    Σ G (λ n →
      SubgroupOf.member N n ×
      (Group.multiply structure h n ≡ x)))

DoubleQuotientRelated :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  (N M : SubgroupOf structure) →
  G →
  G →
  Set ℓ
DoubleQuotientRelated {G = G} structure N M x y =
  Σ G (λ m →
    SubgroupOf.member M m ×
    QuotientRelated structure N m
      (Group.multiply structure (Group.inverse structure x) y))

-- Lean: QuotientGroup.quotientKerEquivRange
first-isomorphism-theorem :
  (a b : Level) →
  Set (lsuc (a ⊔ b))
first-isomorphism-theorem a b =
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

-- Lean: QuotientGroup.quotientInfEquivProdNormalQuotient
second-isomorphism-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
second-isomorphism-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (H N : SubgroupOf structure) →
  Normal N →
  RestrictedMulEquiv
    G
    G
    (SubgroupOf.member H)
    (ProductMember structure H N)
    (QuotientRelated structure N)
    (QuotientRelated structure N)
    (Group.multiply structure)
    (Group.multiply structure)
    (λ x → x)

-- Lean: QuotientGroup.quotientQuotientEquivQuotient
third-isomorphism-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
third-isomorphism-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  (N M : SubgroupOf structure) →
  Normal N →
  Normal M →
  N ⊆ M →
  RestrictedMulEquiv
    G
    G
    (λ _ → ⊤ {ℓ})
    (λ _ → ⊤ {ℓ})
    (DoubleQuotientRelated structure N M)
    (QuotientRelated structure M)
    (Group.multiply structure)
    (Group.multiply structure)
    (λ x → x)
