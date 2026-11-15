-- Statement-only formalization of thousand-theorems corpus artifact Q33481
-- (thousand-theorems__agda__Q33481), "Arrow's impossibility theorem": every
-- social welfare function on at least three alternatives that satisfies Weak
-- Pareto and independence of irrelevant alternatives is dictatorial. This
-- file contains no proof.

{-# OPTIONS --safe #-}

module Q33481_arrow_s_impossibility_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)

infixr 4 _×_
infix  2 _↔_

data Bottom {p : Level} : Set p where

Not :
  {p : Level} →
  Set p →
  Set p
Not {p} proposition =
  proposition → Bottom {p}

record _×_
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  constructor both
  field
    first  : left-proposition
    second : right-proposition

data Either
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  left-case  : left-proposition → Either left-proposition right-proposition
  right-case : right-proposition → Either left-proposition right-proposition

record _↔_
  {p q : Level}
  (left-proposition : Set p)
  (right-proposition : Set q) :
  Set (p ⊔ q) where

  constructor equivalence
  field
    forward  : left-proposition → right-proposition
    backward : right-proposition → left-proposition

record Exists
  {a p : Level}
  (A : Set a)
  (property : A → Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value     : A
    satisfies : property value

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

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size        : Nat
    enumeration : Bijection A (Fin size)

record FiniteSubset
  {a : Level}
  (A : Set a) :
  Set a where

  field
    size      : Nat
    enumerate : Fin size → A
    injective :
      (i j : Fin size) →
      enumerate i ≡ enumerate j →
      i ≡ j

open FiniteSubset

Member :
  {a : Level} →
  {A : Set a} →
  FiniteSubset A →
  A →
  Set a
Member subset x =
  Exists (Fin (size subset))
    (λ index → enumerate subset index ≡ x)

AtLeastThree :
  {a : Level} →
  {A : Set a} →
  FiniteSubset A →
  Set
AtLeastThree subset =
  Exists Nat
    (λ remaining →
      size subset ≡ suc (suc (suc remaining)))

record PreferenceOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    relation :
      A →
      A →
      Set a
    reflexive :
      (x : A) →
      relation x x
    total :
      (x y : A) →
      Either (relation x y) (relation y x)
    transitive :
      (x y z : A) →
      relation x y →
      relation y z →
      relation x z

open PreferenceOrder

StrictPreference :
  {a : Level} →
  {A : Set a} →
  PreferenceOrder A →
  A →
  A →
  Set a
StrictPreference order x y =
  relation order x y
  ×
  Not (relation order y x)

SameOrderOnPair :
  {a : Level} →
  {A : Set a} →
  PreferenceOrder A →
  PreferenceOrder A →
  A →
  A →
  Set a
SameOrderOnPair left-order right-order x y =
  (StrictPreference left-order x y
    ↔
   StrictPreference right-order x y)
  ×
  (StrictPreference left-order y x
    ↔
   StrictPreference right-order y x)

SocialWelfareFunction :
  {a i : Level} →
  Set i →
  Set a →
  Set (i ⊔ lsuc a)
SocialWelfareFunction Individuals Alternatives =
  (Individuals → PreferenceOrder Alternatives) →
  PreferenceOrder Alternatives

WeakPareto :
  {a i : Level} →
  {Alternatives : Set a} →
  {Individuals : Set i} →
  SocialWelfareFunction Individuals Alternatives →
  FiniteSubset Alternatives →
  Set (i ⊔ lsuc a)
WeakPareto {Alternatives = Alternatives} {Individuals = Individuals}
  social-choice alternatives =
  (x y : Alternatives) →
  Member alternatives x →
  Member alternatives y →
  (profile : Individuals → PreferenceOrder Alternatives) →
  ((individual : Individuals) →
    StrictPreference (profile individual) x y) →
  StrictPreference (social-choice profile) x y

IndependentOfIrrelevantAlternatives :
  {a i : Level} →
  {Alternatives : Set a} →
  {Individuals : Set i} →
  SocialWelfareFunction Individuals Alternatives →
  FiniteSubset Alternatives →
  Set (i ⊔ lsuc a)
IndependentOfIrrelevantAlternatives
  {Alternatives = Alternatives}
  {Individuals = Individuals}
  social-choice alternatives =
  (left-profile right-profile :
    Individuals → PreferenceOrder Alternatives) →
  (x y : Alternatives) →
  Member alternatives x →
  Member alternatives y →
  ((individual : Individuals) →
    SameOrderOnPair
      (left-profile individual)
      (right-profile individual)
      x
      y) →
  SameOrderOnPair
    (social-choice left-profile)
    (social-choice right-profile)
    x
    y

IsDictatorship :
  {a i : Level} →
  {Alternatives : Set a} →
  {Individuals : Set i} →
  SocialWelfareFunction Individuals Alternatives →
  FiniteSubset Alternatives →
  Set (i ⊔ lsuc a)
IsDictatorship {Alternatives = Alternatives} {Individuals = Individuals}
  social-choice alternatives =
  Exists Individuals
    (λ dictator →
      (x y : Alternatives) →
      Member alternatives x →
      Member alternatives y →
      (profile : Individuals → PreferenceOrder Alternatives) →
      StrictPreference (profile dictator) x y →
      StrictPreference (social-choice profile) x y)

arrow-impossibility-theorem :
  {a i : Level} →
  Set (lsuc (a ⊔ i))
arrow-impossibility-theorem {a} {i} =
  (Alternatives : Set a) →
  (Individuals : Set i) →
  Finite Individuals →
  (alternatives : FiniteSubset Alternatives) →
  (social-choice :
    SocialWelfareFunction Individuals Alternatives) →
  WeakPareto social-choice alternatives →
  IndependentOfIrrelevantAlternatives social-choice alternatives →
  AtLeastThree alternatives →
  IsDictatorship social-choice alternatives
