-- Statement-only formalization of Hundred Theorems artifact hundred-theorems__agda__073,
-- "Ascending or Descending Sequences (Erdős–Szekeres)": every sequence of m*n+1 values in a
-- linear order has a nondecreasing subsequence of length m+1 or a strictly decreasing
-- subsequence of length n+1. This file contains no proof.

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)

infix 4 _<F_
infixr 4 _∧_
infixr 3 _∨_

data Bottom : Set where

Not :
  {a : Level} →
  Set a →
  Set a
Not proposition =
  proposition → Bottom

record _∧_
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a ⊔ b) where

  constructor both
  field
    first : left
    second : right

data _∨_
  {a b : Level}
  (left : Set a)
  (right : Set b) :
  Set (a ⊔ b) where

  left-case : left → left ∨ right
  right-case : right → left ∨ right

data Comparison
  {a : Level}
  {A : Set a}
  (_≤_ : A → A → Set a)
  (x y : A) :
  Set a where

  less :
    _≤_ x y →
    Not (x ≡ y) →
    Comparison _≤_ x y
  equal :
    x ≡ y →
    Comparison _≤_ x y
  greater :
    _≤_ y x →
    Not (y ≡ x) →
    Comparison _≤_ x y

record LinearOrder
  {a : Level}
  (A : Set a) :
  Set (lsuc a) where

  field
    less-or-equal : A → A → Set a
    reflexive :
      (x : A) →
      less-or-equal x x
    antisymmetric :
      (x y : A) →
      less-or-equal x y →
      less-or-equal y x →
      x ≡ y
    transitive :
      (x y z : A) →
      less-or-equal x y →
      less-or-equal y z →
      less-or-equal x z
    total :
      (x y : A) →
      less-or-equal x y ∨ less-or-equal y x
    compare :
      (x y : A) →
      Comparison less-or-equal x y

strict-less :
  {a : Level} →
  {A : Set a} →
  LinearOrder A →
  A →
  A →
  Set a
strict-less order x y =
  LinearOrder.less-or-equal order x y ∧
  Not (x ≡ y)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data _<F_ : {n : Nat} → Fin n → Fin n → Set where
  zero-less-successor :
    {n : Nat} →
    {j : Fin n} →
    fzero <F fsuc j
  successor-less-successor :
    {n : Nat} →
    {i j : Fin n} →
    i <F j →
    fsuc i <F fsuc j

record NondecreasingSubsequence
  {a : Level}
  {A : Set a}
  (order : LinearOrder A)
  {bound length : Nat}
  (sequence : Fin bound → A) :
  Set a where

  field
    position : Fin length → Fin bound
    positions-increase :
      (i j : Fin length) →
      i <F j →
      position i <F position j
    values-nondecrease :
      (i j : Fin length) →
      i <F j →
      LinearOrder.less-or-equal order
        (sequence (position i))
        (sequence (position j))

record StrictlyDecreasingSubsequence
  {a : Level}
  {A : Set a}
  (order : LinearOrder A)
  {bound length : Nat}
  (sequence : Fin bound → A) :
  Set a where

  field
    position : Fin length → Fin bound
    positions-increase :
      (i j : Fin length) →
      i <F j →
      position i <F position j
    values-decrease :
      (i j : Fin length) →
      i <F j →
      strict-less order
        (sequence (position j))
        (sequence (position i))

ascending-or-descending-sequences :
  {a : Level} →
  Set (lsuc a)
ascending-or-descending-sequences {a} =
  (A : Set a) →
  (order : LinearOrder A) →
  (m n : Nat) →
  (sequence : Fin (suc (m * n)) → A) →
  NondecreasingSubsequence
    order
    {length = suc m}
    sequence
  ∨
  StrictlyDecreasingSubsequence
    order
    {length = suc n}
    sequence
