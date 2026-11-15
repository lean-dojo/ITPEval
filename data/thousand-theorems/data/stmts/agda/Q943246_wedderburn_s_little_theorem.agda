-- Statement-only formalization of thousand-theorems corpus artifact Q943246,
-- "Wedderburn's little theorem": every finite division ring has commutative
-- multiplication and hence is a field. This file contains no proof.

{-# OPTIONS --safe #-}

module Q943246_wedderburn_s_little_theorem where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; _∷_)

data Empty : Set where

Not : {a : Level} → Set a → Set a
Not A = A → Empty

infix 4 _≠_

_≠_ : {a : Level} {A : Set a} → A → A → Set a
x ≠ y = Not (x ≡ y)

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

record Finite
  {a : Level}
  (A : Set a) :
  Set a where

  field
    enumeration : List A
    exhaustive  : (x : A) → Member x enumeration

record Ring
  {a : Level}
  (A : Set a) :
  Set a where

  field
    zero one : A
    add multiply : A → A → A
    negate : A → A

    add-associative :
      (x y z : A) →
      add (add x y) z ≡ add x (add y z)
    add-commutative :
      (x y : A) →
      add x y ≡ add y x
    add-zero-left :
      (x : A) →
      add zero x ≡ x
    add-zero-right :
      (x : A) →
      add x zero ≡ x
    add-inverse-left :
      (x : A) →
      add (negate x) x ≡ zero
    add-inverse-right :
      (x : A) →
      add x (negate x) ≡ zero

    multiply-associative :
      (x y z : A) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one-left :
      (x : A) →
      multiply one x ≡ x
    multiply-one-right :
      (x : A) →
      multiply x one ≡ x

    distribute-left :
      (x y z : A) →
      multiply x (add y z) ≡ add (multiply x y) (multiply x z)
    distribute-right :
      (x y z : A) →
      multiply (add x y) z ≡ add (multiply x z) (multiply y z)

record DivisionRing
  {a : Level}
  (A : Set a) :
  Set a where

  field
    ring : Ring A
    inverse : A → A
    nontrivial : Ring.zero ring ≠ Ring.one ring
    inverse-zero :
      inverse (Ring.zero ring) ≡ Ring.zero ring
    inverse-left :
      (x : A) →
      x ≠ Ring.zero ring →
      Ring.multiply ring (inverse x) x ≡ Ring.one ring
    inverse-right :
      (x : A) →
      x ≠ Ring.zero ring →
      Ring.multiply ring x (inverse x) ≡ Ring.one ring

record IsField
  {a : Level}
  {A : Set a}
  (division : DivisionRing A) :
  Set a where

  field
    multiply-commutative :
      (x y : A) →
      Ring.multiply (DivisionRing.ring division) x y ≡
      Ring.multiply (DivisionRing.ring division) y x

littleWedderburn :
  (a : Level) →
  Set (lsuc a)
littleWedderburn a =
  (D : Set a) →
  (division : DivisionRing D) →
  Finite D →
  IsField division
