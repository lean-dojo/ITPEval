-- Statement-only formalization of miniF2F valid problem mathd_algebra_185. This file contains
-- no proof.

module mathd-algebra-185 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infixl 6 _+z_
infix 4 _<n_ _<z_ _∈_ _∈ₛ_
infix 2 _↔_

data ⊥ : Set where

record ⊤ : Set where
  constructor trivial

record _↔_ (A B : Set) : Set where
  field
    forward  : A → B
    backward : B → A

data _<n_ : Nat → Nat → Set where
  zero-less-successor :
    {n : Nat} →
    zero <n suc n
  successor-less-successor :
    {m n : Nat} →
    m <n n →
    suc m <n suc n

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

_+z_ : Int → Int → Int
pos m +z pos n = pos (m + n)
pos m +z negsuc n = difference m (suc n)
negsuc m +z pos n = difference n (suc m)
negsuc m +z negsuc n = negsuc (suc (m + n))

absoluteValue : Int → Int
absoluteValue (pos n) = pos n
absoluteValue (negsuc n) = pos (suc n)

_<z_ : Int → Int → Set
pos m <z pos n = m <n n
pos m <z negsuc n = ⊥
negsuc m <z pos n = ⊤
negsuc m <z negsuc n = n <n m

data _∈_ {A : Set} (x : A) : List A → Set where
  here :
    {y : A} {ys : List A} →
    x ≡ y →
    x ∈ (y ∷ ys)
  there :
    {y : A} {ys : List A} →
    x ∈ ys →
    x ∈ (y ∷ ys)

data NoDuplicates {A : Set} : List A → Set where
  no-duplicates-empty :
    NoDuplicates []
  no-duplicates-cons :
    {x : A} {xs : List A} →
    (x ∈ xs → ⊥) →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

record FiniteSet (A : Set) : Set where
  field
    elements     : List A
    noDuplicates : NoDuplicates elements

_∈ₛ_ : {A : Set} → A → FiniteSet A → Set
x ∈ₛ s = x ∈ FiniteSet.elements s

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

cardinality : {A : Set} → FiniteSet A → Nat
cardinality s = length (FiniteSet.elements s)

mathd-algebra-185 : Set
mathd-algebra-185 =
  (s : FiniteSet Int) →
  (f : Int → Int) →
  ((x : Int) →
    f x ≡ absoluteValue (x +z pos 4)) →
  ((x : Int) →
    (x ∈ₛ s) ↔ (f x <z pos 9)) →
  cardinality s ≡ 17
