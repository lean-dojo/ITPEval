-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc: the
-- final linked-list reversal verification condition relating forward and
-- reversed list layouts while preserving the memory frame. This file contains no proof.

{-# OPTIONS --safe #-}

module linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

negative : Nat → Int
negative zero = pos zero
negative (suc n) = negsuc n

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

record Mem (Loc : Set) : Set where
  constructor mem
  field
    next : Loc → Loc

open Mem

shift :
  {A : Set} →
  (Int → A) →
  Int →
  A
shift s i = s (addInt i oneZ)

reverseIndexing :
  {A : Set} →
  (Int → A) →
  Int →
  Int →
  A
reverseIndexing s n i =
  s (subtractInt (subtractInt n oneZ) i)

record LinkedListTheory : Set₁ where
  field
    Loc    : Set
    null   : Loc
    IsList : Mem Loc → Loc → (Int → Loc) → Int → Set

    isListDef :
      (n : Int) →
      (m : Mem Loc) →
      (l : Loc) →
      (s : Int → Loc) →
      zeroZ ≤Z n →
      IsList m l s n
        ↔
      IfSet
        (intEqual n zeroZ)
        (l ≡ null)
        ((l ≡ s zeroZ ∧ s zeroZ ≢ null)
         ∧ IsList
             m
             (next m l)
             (shift s)
             (subtractInt n oneZ))

open LinkedListTheory

Range : Int → Int → Set
Range i n = zeroZ ≤Z i ∧ i <Z n

ValidCells :
  (theory : LinkedListTheory) →
  (Int → Loc theory) →
  Int →
  Set
ValidCells theory s n =
  ((i : Int) →
    Range i n →
    s i ≢ null theory)
  ∧
  ((i j : Int) →
    Range i n →
    Range j n →
    i ≢ j →
    s i ≢ s j)

ListLR :
  (theory : LinkedListTheory) →
  Mem (Loc theory) →
  (Int → Loc theory) →
  Loc theory →
  Int →
  Int →
  Set
ListLR theory m s l lo hi =
  (zeroZ ≤Z lo ∧ lo ≤Z hi)
  ∧
  IfSet
    (intEqual lo hi)
    (l ≡ null theory)
    (l ≡ s lo
     ∧ next m (s (subtractInt hi oneZ)) ≡ null theory
     ∧
     ((k : Int) →
       (lo ≤Z k ∧ k <Z subtractInt hi oneZ) →
       next m (s k) ≡ s (addInt k oneZ)))

ListRL :
  (theory : LinkedListTheory) →
  Mem (Loc theory) →
  (Int → Loc theory) →
  Loc theory →
  Int →
  Int →
  Set
ListRL theory m s l lo hi =
  (zeroZ ≤Z lo ∧ lo ≤Z hi)
  ∧
  IfSet
    (intEqual lo hi)
    (l ≡ null theory)
    (next m (s lo) ≡ null theory
     ∧ l ≡ s (subtractInt hi oneZ)
     ∧
     ((k : Int) →
       (lo <Z k ∧ k <Z hi) →
       next m (s k) ≡ s (subtractInt k oneZ)))

Frame :
  (theory : LinkedListTheory) →
  Mem (Loc theory) →
  Mem (Loc theory) →
  (Int → Loc theory) →
  Int →
  Set
Frame theory m₁ m₂ s n =
  (p : Loc theory) →
  ((i : Int) →
    Range i n →
    p ≢ s i)
  →
  next m₁ p ≡ next m₂ p

list-reversal-final'vc : Set₁
list-reversal-final'vc =
  (theory : LinkedListTheory) →
  (mem₁ : Loc theory → Loc theory) →
  (s : Int → Loc theory) →
  (n : Int) →
  (l : Loc theory) →
  (zeroZ ≤Z n
   ∧ IsList theory (mem mem₁) l s n)
  →
  (ValidCells theory s n
   ∧ ListLR theory (mem mem₁) s l zeroZ n)
  ∧
  ((mem₃ : Loc theory → Loc theory) →
   (r : Loc theory) →
   (ListRL theory (mem mem₃) s r zeroZ n
    ∧ Frame theory (mem mem₃) (mem mem₁) s n)
   →
   (IsList
      theory
      (mem mem₃)
      r
      (reverseIndexing s n)
      n
    ∧ Frame theory (mem mem₃) (mem mem₁) s n))
