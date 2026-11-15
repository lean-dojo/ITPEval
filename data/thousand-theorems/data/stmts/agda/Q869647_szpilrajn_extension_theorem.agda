-- Statement-only formalization of thousand-theorems corpus artifact Q869647
-- (thousand-theorems__agda__Q869647), "Szpilrajn extension theorem": every
-- partial-order relation on an arbitrary type has a linear-order extension
-- containing the original relation. This file contains no proof.

{-# OPTIONS --safe #-}

module Q869647_szpilrajn_extension_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

record HProp (p : Level) : Set (lsuc p) where
  constructor proposition
  field
    Carrier : Set p
    carrier-is-proposition :
      (left right : Carrier) →
      left ≡ right

open HProp using (Carrier)

Relation :
  {a : Level} →
  (p : Level) →
  Set a →
  Set (a ⊔ lsuc p)
Relation p A =
  A → A → HProp p

data Either
  {p q : Level}
  (P : Set p)
  (Q : Set q) :
  Set (p ⊔ q) where

  left  : P → Either P Q
  right : Q → Either P Q

record IsPartialOrder
  {a p : Level}
  {A : Set a}
  (relation : Relation p A) :
  Set (a ⊔ p) where

  field
    reflexive :
      (x : A) →
      Carrier (relation x x)
    transitive :
      (x y z : A) →
      Carrier (relation x y) →
      Carrier (relation y z) →
      Carrier (relation x z)
    antisymmetric :
      (x y : A) →
      Carrier (relation x y) →
      Carrier (relation y x) →
      x ≡ y

record IsLinearOrder
  {a p : Level}
  {A : Set a}
  (relation : Relation p A) :
  Set (a ⊔ p) where

  field
    partial-order :
      IsPartialOrder relation
    total :
      (x y : A) →
      Either
        (Carrier (relation x y))
        (Carrier (relation y x))

Extends :
  {a p : Level}
  {A : Set a} →
  Relation p A →
  Relation p A →
  Set (a ⊔ p)
Extends original extension =
  (x y : _) →
  Carrier (original x y) →
  Carrier (extension x y)

record LinearExtension
  {a p : Level}
  {A : Set a}
  (original : Relation p A) :
  Set (a ⊔ lsuc p) where

  constructor linear-extension
  field
    extension-relation :
      Relation p A
    extension-is-linear :
      IsLinearOrder extension-relation
    contains-original :
      Extends original extension-relation

szpilrajn-extension-theorem :
  {a p : Level} →
  Set (lsuc (a ⊔ p))
szpilrajn-extension-theorem {a} {p} =
  (A : Set a) →
  (relation : Relation p A) →
  IsPartialOrder relation →
  LinearExtension relation
