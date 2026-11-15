-- Statement-only formalization of thousand-theorems corpus artifact Q253214,
-- "Heine–Borel theorem": in a proper metric space, a set is compact if and
-- only if it is closed and bounded. This file contains no proof.

{-# OPTIONS --safe #-}

module Q253214_heine_borel_theorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat) renaming (zero to zeroN; suc to sucN)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≠_
infixr 3 _×_

data Bottom {a : Level} : Set a where

Not :
  {a : Level} →
  Set a →
  Set a
Not {a} proposition =
  proposition → Bottom {a}

_≠_ :
  {a : Level} →
  {A : Set a} →
  A →
  A →
  Set a
x ≠ y =
  Not (x ≡ y)

record _×_
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first  : A
    second : B

record Iff
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  constructor equivalence
  field
    forward  : A → B
    backward : B → A

data Either
  {a b : Level}
  (A : Set a)
  (B : Set b) :
  Set (a ⊔ b) where

  left  : A → Either A B
  right : B → Either A B

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
    {y : A} →
    {xs : List A} →
    Member x xs →
    Member x (y ∷ xs)

-- A complete Archimedean ordered field is a presentation of the real line.
record RealLine
  {r : Level}
  (R : Set r) :
  Set (lsuc r) where

  field
    zero one :
      R

    add multiply :
      R →
      R →
      R

    negate reciprocal :
      R →
      R

    lessOrEqual :
      R →
      R →
      Set r

    fromNat :
      Nat →
      R

    one-not-zero :
      one ≠ zero

    add-commutative :
      (x y : R) →
      add x y ≡ add y x

    add-associative :
      (x y z : R) →
      add (add x y) z ≡ add x (add y z)

    add-zero :
      (x : R) →
      add x zero ≡ x

    add-inverse :
      (x : R) →
      add x (negate x) ≡ zero

    multiply-commutative :
      (x y : R) →
      multiply x y ≡ multiply y x

    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)

    multiply-one :
      (x : R) →
      multiply x one ≡ x

    multiply-zero :
      (x : R) →
      multiply x zero ≡ zero

    distribute :
      (x y z : R) →
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)

    multiply-reciprocal :
      (x : R) →
      x ≠ zero →
      multiply x (reciprocal x) ≡ one

    order-reflexive :
      (x : R) →
      lessOrEqual x x

    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z

    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y

    order-total :
      (x y : R) →
      Either (lessOrEqual x y) (lessOrEqual y x)

    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)

    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zero x →
      lessOrEqual zero y →
      lessOrEqual zero (multiply x y)

    zero-less-than-one :
      lessOrEqual zero one × zero ≠ one

    fromNat-zero :
      fromNat zeroN ≡ zero

    fromNat-successor :
      (n : Nat) →
      fromNat (sucN n) ≡ add (fromNat n) one

    fromNat-injective :
      (m n : Nat) →
      fromNat m ≡ fromNat n →
      m ≡ n

    archimedean :
      (x : R) →
      Σ Nat (λ n → lessOrEqual x (fromNat n))

    least-upper-bound :
      (P : R → Set r) →
      Σ R P →
      Σ R (λ upper → (x : R) → P x → lessOrEqual x upper) →
      Σ R
        (λ supremum →
          ((x : R) → P x → lessOrEqual x supremum)
          ×
          ((upper : R) →
            ((x : R) → P x → lessOrEqual x upper) →
            lessOrEqual supremum upper))

open RealLine

StrictLess :
  {r : Level} →
  {R : Set r} →
  RealLine R →
  R →
  R →
  Set r
StrictLess reals x y =
  lessOrEqual reals x y × x ≠ y

record MetricSpace
  {r a : Level}
  {R : Set r}
  (reals : RealLine R)
  (X : Set a) :
  Set (r ⊔ a) where

  field
    distance :
      X →
      X →
      R

    distance-nonnegative :
      (x y : X) →
      lessOrEqual reals (zero reals) (distance x y)

    distance-self :
      (x : X) →
      distance x x ≡ zero reals

    distance-zero-only :
      (x y : X) →
      distance x y ≡ zero reals →
      x ≡ y

    distance-symmetric :
      (x y : X) →
      distance x y ≡ distance y x

    distance-triangle :
      (x y z : X) →
      lessOrEqual reals
        (distance x z)
        (add reals (distance x y) (distance y z))

open MetricSpace

Subset :
  {a p : Level} →
  Set a →
  Set (a ⊔ lsuc p)
Subset {p = p} X =
  X → Set p

Family :
  {a p : Level} →
  Set a →
  Set (a ⊔ lsuc p)
Family {p = p} X =
  Subset {p = p} X → Set p

Complement :
  {a p : Level} →
  {X : Set a} →
  Subset {p = p} X →
  Subset {p = p} X
Complement U x =
  Not (U x)

IsOpen :
  {r a : Level} →
  {R : Set r} →
  {X : Set a} →
  {reals : RealLine R} →
  MetricSpace reals X →
  Subset {p = r} X →
  Set (r ⊔ a)
IsOpen {R = R} {X = X} {reals = reals} metric U =
  (center : X) →
  U center →
  Σ R
    (λ radius →
      StrictLess reals (zero reals) radius
      ×
      ((point : X) →
        StrictLess reals (distance metric center point) radius →
        U point))

IsClosed :
  {r a : Level} →
  {R : Set r} →
  {X : Set a} →
  {reals : RealLine R} →
  MetricSpace reals X →
  Subset {p = r} X →
  Set (r ⊔ a)
IsClosed metric U =
  IsOpen metric (Complement U)

Covers :
  {a p : Level} →
  {X : Set a} →
  Subset {p = p} X →
  Family {p = p} X →
  Set (a ⊔ lsuc p)
Covers {p = p} {X = X} U cover =
  (x : X) →
  U x →
  Σ (Subset {p = p} X)
    (λ V →
      cover V × V x)

FiniteSubcover :
  {a p : Level} →
  {X : Set a} →
  Subset {p = p} X →
  Family {p = p} X →
  Set (a ⊔ lsuc p)
FiniteSubcover {p = p} {X = X} U cover =
  Σ (List (Subset {p = p} X))
    (λ selected →
      ((V : Subset {p = p} X) →
        Member V selected →
        cover V)
      ×
      ((x : X) →
        U x →
        Σ (Subset {p = p} X)
          (λ V →
            Member V selected × V x)))

Compact :
  {r a : Level} →
  {R : Set r} →
  {X : Set a} →
  {reals : RealLine R} →
  MetricSpace reals X →
  Subset {p = r} X →
  Set (a ⊔ lsuc r)
Compact {r = r} {X = X} metric U =
  (cover : Family {p = r} X) →
  ((V : Subset {p = r} X) →
    cover V →
    IsOpen metric V) →
  Covers U cover →
  FiniteSubcover U cover

IsBounded :
  {r a : Level} →
  {R : Set r} →
  {X : Set a} →
  {reals : RealLine R} →
  MetricSpace reals X →
  Subset {p = r} X →
  Set (r ⊔ a)
IsBounded {R = R} {X = X} {reals = reals} metric U =
  Σ R
    (λ bound →
      (x y : X) →
      U x →
      U y →
      lessOrEqual reals (distance metric x y) bound)

ClosedBall :
  {r a : Level} →
  {R : Set r} →
  {X : Set a} →
  {reals : RealLine R} →
  MetricSpace reals X →
  X →
  R →
  Subset {p = r} X
ClosedBall {reals = reals} metric center radius point =
  lessOrEqual reals (distance metric center point) radius

Proper :
  {r a : Level} →
  {R : Set r} →
  {X : Set a} →
  {reals : RealLine R} →
  MetricSpace reals X →
  Set (a ⊔ lsuc r)
Proper {R = R} {X = X} metric =
  (center : X) →
  (radius : R) →
  Compact metric (ClosedBall metric center radius)

heine-borel-theorem :
  {r a : Level} →
  Set (lsuc (r ⊔ a))
heine-borel-theorem {r} {a} =
  (R : Set r) →
  (reals : RealLine R) →
  (X : Set a) →
  (metric : MetricSpace reals X) →
  Proper metric →
  (U : Subset {p = r} X) →
  Iff
    (Compact metric U)
    (IsClosed metric U × IsBounded metric U)
