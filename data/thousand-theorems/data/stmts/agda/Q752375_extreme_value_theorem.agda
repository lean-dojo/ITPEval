-- Statement-only formalization of thousand-theorems corpus artifact Q752375,
-- "Extreme value theorem": a continuous function into a linearly ordered
-- topological space with closed lower rays attains its minimum on every
-- nonempty compact subset of its domain. This file contains no proof.

{-# OPTIONS --safe #-}

module Q752375_extreme_value_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ)

infixr 3 _×_

data Bottom {a : Level} : Set a where

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

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → Either A B
  right : B → Either A B

record Exists
  {a p : Level}
  (A : Set a)
  (P : A → Set p) :
  Set (a ⊔ p) where

  constructor witness
  field
    value    : A
    property : P value

data Member
  {a : Level}
  {A : Set a}
  (x : A) :
  List A →
  Set a where

  at-head :
    {xs : List A} →
    Member x (x ∷ xs)

  in-tail :
    {y : A}
    {xs : List A} →
    Member x xs →
    Member x (y ∷ xs)

Subset :
  {a : Level} →
  Set a →
  Set (lsuc a)
Subset {a} X =
  X → Set a

Family :
  {a : Level} →
  Set a →
  Set (lsuc a)
Family {a} X =
  Subset X → Set a

Empty :
  {a : Level}
  {X : Set a} →
  Subset X
Empty {a} _ =
  Bottom {a}

Union :
  {a : Level}
  {X : Set a} →
  Subset X →
  Subset X →
  Subset X
Union U V x =
  Either (U x) (V x)

Complement :
  {a : Level}
  {X : Set a} →
  Subset X →
  Subset X
Complement U x =
  Not (U x)

SubsetOf :
  {a : Level}
  {X : Set a} →
  Subset X →
  Subset X →
  Set a
SubsetOf {X = X} U V =
  (x : X) →
  U x →
  V x

record TopologicalSpace
  {a : Level}
  (X : Set a) :
  Set (lsuc a) where

  field
    close :
      Subset X →
      Subset X

    close-empty :
      SubsetOf (close Empty) Empty

    subset-close :
      (U : Subset X) →
      SubsetOf U (close U)

    close-monotone :
      (U V : Subset X) →
      SubsetOf U V →
      SubsetOf (close U) (close V)

    close-union-forward :
      (U V : Subset X) →
      SubsetOf
        (close (Union U V))
        (Union (close U) (close V))

    close-union-backward :
      (U V : Subset X) →
      SubsetOf
        (Union (close U) (close V))
        (close (Union U V))

    close-idempotent :
      (U : Subset X) →
      SubsetOf (close (close U)) (close U)

open TopologicalSpace

IsClosed :
  {a : Level}
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set a
IsClosed topology U =
  SubsetOf (close topology U) U

IsOpen :
  {a : Level}
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set a
IsOpen topology U =
  IsClosed topology (Complement U)

Covers :
  {a : Level}
  {X : Set a} →
  Subset X →
  Family X →
  Set (lsuc a)
Covers {X = X} U cover =
  (x : X) →
  U x →
  Σ (Subset X)
    (λ V →
      cover V × V x)

FiniteSubcover :
  {a : Level}
  {X : Set a} →
  Subset X →
  Family X →
  Set (lsuc a)
FiniteSubcover {X = X} U cover =
  Σ (List (Subset X))
    (λ selected →
      ((V : Subset X) →
        Member V selected →
        cover V)
      ×
      ((x : X) →
        U x →
        Σ (Subset X)
          (λ V →
            Member V selected × V x)))

Compact :
  {a : Level}
  {X : Set a} →
  TopologicalSpace X →
  Subset X →
  Set (lsuc a)
Compact {X = X} topology U =
  (cover : Family X) →
  ((V : Subset X) →
    cover V →
    IsOpen topology V) →
  Covers U cover →
  FiniteSubcover U cover

Nonempty :
  {a : Level}
  {X : Set a} →
  Subset X →
  Set a
Nonempty {X = X} U =
  Exists X U

record LinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    lessOrEqual :
      A →
      A →
      Set a

    order-reflexive :
      (x : A) →
      lessOrEqual x x

    order-transitive :
      (x y z : A) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z

    order-antisymmetric :
      (x y : A) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y

    order-total :
      (x y : A) →
      Either
        (lessOrEqual x y)
        (lessOrEqual y x)

open LinearOrder

LowerRay :
  {a : Level}
  {A : Set a} →
  LinearOrder A →
  A →
  Subset A
LowerRay order upper x =
  lessOrEqual order x upper

record ClosedLowerRays
  {a : Level}
  {A : Set a}
  (order : LinearOrder A)
  (topology : TopologicalSpace A) :
  Set (lsuc a) where

  field
    lower-ray-closed :
      (upper : A) →
      IsClosed topology (LowerRay order upper)

ContinuousOn :
  {a b : Level}
  {A : Set a}
  {B : Set b} →
  TopologicalSpace A →
  TopologicalSpace B →
  (A → B) →
  Subset A →
  Set (lsuc (a ⊔ b))
ContinuousOn {A = A} {B = B} source target f domain =
  (x : A) →
  domain x →
  (V : Subset B) →
  IsOpen target V →
  V (f x) →
  Exists (Subset A)
    (λ U →
      IsOpen source U
      ×
      (U x
      ×
      ((y : A) →
        domain y →
        U y →
        V (f y))))

IsMinOn :
  {a b : Level}
  {A : Set a}
  {B : Set b} →
  LinearOrder B →
  (A → B) →
  Subset A →
  A →
  Set (a ⊔ b)
IsMinOn {A = A} order f domain x =
  (y : A) →
  domain y →
  lessOrEqual order (f x) (f y)

extreme-value-theorem :
  {a b : Level} →
  Set (lsuc (a ⊔ b))
extreme-value-theorem {a} {b} =
  (A : Set a) →
  (B : Set b) →
  (order : LinearOrder A) →
  (target : TopologicalSpace A) →
  ClosedLowerRays order target →
  (source : TopologicalSpace B) →
  (domain : Subset B) →
  Compact source domain →
  Nonempty domain →
  (f : B → A) →
  ContinuousOn source target f domain →
  Exists B
    (λ x →
      domain x
      ×
      IsMinOn order f domain x)
