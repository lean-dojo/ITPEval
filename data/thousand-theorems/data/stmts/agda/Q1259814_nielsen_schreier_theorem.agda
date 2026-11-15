-- Statement-only formalization of thousand-theorems corpus artifact Q1259814,
-- "Nielsen–Schreier theorem": every subgroup of a free group is itself a free
-- group. This file contains no proof.

module Q1259814_nielsen_schreier_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

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

record MultiplicativeHom
  {a b : Level}
  (A : Set a)
  (B : Set b)
  (multiply-A : A → A → A)
  (multiply-B : B → B → B) :
  Set (a ⊔ b) where

  field
    map : A → B
    map-multiply :
      (x y : A) →
      map (multiply-A x y) ≡ multiply-B (map x) (map y)

record UniqueExtension
  {ℓ : Level}
  {A X K : Set ℓ}
  (multiply-A : A → A → A)
  (target : Group K)
  (include : X → A)
  (assignment : X → K) :
  Set ℓ where

  field
    extension :
      MultiplicativeHom A K multiply-A (Group.multiply target)
    extends-assignment :
      (x : X) →
      MultiplicativeHom.map extension (include x) ≡ assignment x
    unique :
      (other :
        MultiplicativeHom A K multiply-A (Group.multiply target)) →
      ((x : X) →
        MultiplicativeHom.map other (include x) ≡ assignment x) →
      (a : A) →
      MultiplicativeHom.map other a ≡
      MultiplicativeHom.map extension a

record FreeGroupStructure
  {ℓ : Level}
  (A : Set ℓ)
  (multiply-A : A → A → A) :
  Set (lsuc ℓ) where

  field
    Generators : Set ℓ
    include : Generators → A
    universal-property :
      {K : Set ℓ} →
      (target : Group K) →
      (assignment : Generators → K) →
      UniqueExtension multiply-A target include assignment

IsFreeGroup :
  {ℓ : Level} →
  {G : Set ℓ} →
  Group G →
  Set (lsuc ℓ)
IsFreeGroup {G = G} structure =
  FreeGroupStructure G (Group.multiply structure)

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

SubgroupCarrier :
  {ℓ : Level} →
  {G : Set ℓ} →
  {structure : Group G} →
  SubgroupOf structure →
  Set ℓ
SubgroupCarrier {G = G} H =
  Σ G (SubgroupOf.member H)

subgroupMultiply :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  (H : SubgroupOf structure) →
  SubgroupCarrier H →
  SubgroupCarrier H →
  SubgroupCarrier H
subgroupMultiply structure H (x , hx) (y , hy) =
  Group.multiply structure x y ,
  SubgroupOf.closed-under-multiply H x y hx hy

IsFreeSubgroup :
  {ℓ : Level} →
  {G : Set ℓ} →
  (structure : Group G) →
  SubgroupOf structure →
  Set (lsuc ℓ)
IsFreeSubgroup structure H =
  FreeGroupStructure
    (SubgroupCarrier H)
    (subgroupMultiply structure H)

-- Lean: subgroupIsFreeOfIsFree
nielsen-schreier-theorem :
  (ℓ : Level) →
  Set (lsuc ℓ)
nielsen-schreier-theorem ℓ =
  {G : Set ℓ} →
  (structure : Group G) →
  IsFreeGroup structure →
  (H : SubgroupOf structure) →
  IsFreeSubgroup structure H
