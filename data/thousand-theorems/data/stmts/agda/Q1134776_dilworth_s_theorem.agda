-- Statement-only formalization of thousand-theorems corpus artifact Q1134776
-- (thousand-theorems__agda__Q1134776), "Dilworth's theorem": in every finite
-- partial order, the minimum size of a chain partition equals the maximum
-- size of an antichain. This file contains no proof.

{-# OPTIONS --safe #-}

module Q1134776_dilworth_s_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

infixr 3 _and_
infix 4 _≤_

data Bottom : Set where

Not :
  {p : Level} →
  Set p →
  Set p
Not proposition =
  proposition → Bottom

record _and_
  {p q : Level}
  (P : Set p)
  (Q : Set q) :
  Set (p ⊔ q) where

  constructor both
  field
    first  : P
    second : Q

data Either
  {p q : Level}
  (P : Set p)
  (Q : Set q) :
  Set (p ⊔ q) where

  left  : P → Either P Q
  right : Q → Either P Q

record Exists
  {a p : Level}
  (A : Set a)
  (P : A → Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data _≤_ : Nat → Nat → Set where
  zero≤   : {n : Nat} → zero ≤ n
  suc≤suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

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

Finite :
  {a : Level} →
  Set a →
  Set a
Finite A =
  Exists Nat (λ cardinality → Bijection A (Fin cardinality))

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

record ChainPartition
  {a p : Level}
  {A : Set a}
  (relation : Relation p A)
  (number-of-chains : Nat) :
  Set (a ⊔ p) where

  field
    chain-index :
      A →
      Fin number-of-chains
    every-chain-used :
      (index : Fin number-of-chains) →
      Exists A (λ x → chain-index x ≡ index)
    each-fiber-is-chain :
      (x y : A) →
      Not (x ≡ y) →
      chain-index x ≡ chain-index y →
      Either
        (Carrier (relation x y))
        (Carrier (relation y x))

record Antichain
  {a p : Level}
  {A : Set a}
  (relation : Relation p A)
  (cardinality : Nat) :
  Set (a ⊔ p) where

  field
    element :
      Fin cardinality →
      A
    distinct :
      Injective element
    incomparable :
      (left-index right-index : Fin cardinality) →
      Not (left-index ≡ right-index) →
      Not
        (Carrier
          (relation
            (element left-index)
            (element right-index)))

record IsMinimumChainPartitionSize
  {a p : Level}
  {A : Set a}
  (relation : Relation p A)
  (minimum : Nat) :
  Set (a ⊔ p) where

  field
    attained :
      ChainPartition relation minimum
    least :
      (candidate : Nat) →
      ChainPartition relation candidate →
      minimum ≤ candidate

record IsMaximumAntichainSize
  {a p : Level}
  {A : Set a}
  (relation : Relation p A)
  (maximum : Nat) :
  Set (a ⊔ p) where

  field
    attained :
      Antichain relation maximum
    greatest :
      (candidate : Nat) →
      Antichain relation candidate →
      candidate ≤ maximum

dilworth-s-theorem :
  {a p : Level} →
  Set (lsuc (a ⊔ p))
dilworth-s-theorem {a} {p} =
  (A : Set a) →
  (relation : Relation p A) →
  IsPartialOrder relation →
  Finite A →
  Exists Nat
    (λ optimum →
      IsMinimumChainPartitionSize relation optimum
      and
      IsMaximumAntichainSize relation optimum)
