-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/list_removal_Top_remove2qtvc: the verification condition for removing
-- a non-head entry from a linked list by updating its predecessor pointer,
-- including the traversal and removal branches. This file contains no proof.

{-# OPTIONS --safe #-}

module list_removal_Top_remove2qtvc where

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

notBool : Bool → Bool
notBool true = false
notBool false = true

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

record ListRemovalModel : Set₁ where
  field
    Loc               : Set
    Mem               : Set
    memDefault        : Mem
    null              : Loc
    head              : Loc
    entry             : Loc
    eqLoc             : Loc → Loc → Bool
    eqLocSpec         :
      (x y : Loc) →
      (eqLoc x y ≡ true) ↔ (x ≡ y)
    head-is-not-null  : head ≢ null
    entry-is-not-null : entry ≢ null
    head-is-not-entry : head ≢ entry
    list              : (Loc → Loc) → Loc → Int → Loc → Set
    listDef           :
      (n : Int) →
      (mem₁ : Loc → Loc) →
      (x y : Loc) →
      zeroZ ≤Z n →
      IfSet
        (intEqual n zeroZ)
        (list mem₁ x n y ↔ (x ≡ y))
        (list mem₁ x n y ↔
          (x ≢ null ∧ list mem₁ (mem₁ x) (subtractInt n oneZ) y))

open ListRemovalModel

update :
  (model : ListRemovalModel) →
  (Loc model → Loc model) →
  Loc model →
  Loc model →
  Loc model →
  Loc model
update model old key value query with eqLoc model query key
... | true = value
... | false = old query

AdvanceBranch :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Int →
  Loc model →
  Set
AdvanceBranch model n₁ n₂ mem₁ n ind =
  ind ≢ null model
  ∧
  (zeroZ ≤Z subtractInt n₁ n
   ∧ subtractInt n₁ (addInt n oneZ) <Z subtractInt n₁ n)
  ∧
  (zeroZ <Z addInt n oneZ ∧ addInt n oneZ ≤Z n₁)
  ∧ mem₁ ind ≢ null model
  ∧ list model mem₁
      (head model)
      (subtractInt (addInt n oneZ) oneZ)
      (mem₁ ind)
  ∧ list model mem₁
      (mem₁ (mem₁ ind))
      (subtractInt n₁ (addInt n oneZ))
      (entry model)
  ∧ list model mem₁ (entry model) n₂ (null model)

RemovalBranch :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Loc model →
  Set
RemovalBranch model n₁ n₂ mem₁ ind =
  let o₁ = entry model
  in
  o₁ ≢ null model
  ∧ ind ≢ null model
  ∧ list model
      (update model mem₁ ind (mem₁ o₁))
      (head model)
      (subtractInt (addInt n₁ n₂) oneZ)
      (null model)

LoopStep :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Set
LoopStep model n₁ n₂ mem₁ =
  (n : Int) →
  (ind : Loc model) →
  ((zeroZ <Z n ∧ n ≤Z n₁)
   ∧ ind ≢ null model
   ∧ list model mem₁
      (head model)
      (subtractInt n oneZ)
      ind
   ∧ list model mem₁
      (mem₁ ind)
      (subtractInt n₁ n)
      (entry model)
   ∧ list model mem₁ (entry model) n₂ (null model))
  →
  ind ≢ null model
  ∧ IfSet
      (notBool (eqLoc model (mem₁ ind) (entry model)))
      (AdvanceBranch model n₁ n₂ mem₁ n ind)
      (RemovalBranch model n₁ n₂ mem₁ ind)

remove2'vc : Set₁
remove2'vc =
  (model : ListRemovalModel) →
  (n₁ n₂ : Int) →
  (mem₁ : Loc model → Loc model) →
  zeroZ <Z n₁ →
  zeroZ <Z n₂ →
  list model mem₁ (head model) n₁ (entry model) →
  list model mem₁ (entry model) n₂ (null model) →
  zeroZ <Z oneZ
  ∧ oneZ ≤Z n₁
  ∧ head model ≢ null model
  ∧ list model mem₁
      (head model)
      (subtractInt oneZ oneZ)
      (head model)
  ∧ list model mem₁
      (mem₁ (head model))
      (subtractInt n₁ oneZ)
      (entry model)
  ∧ list model mem₁ (entry model) n₂ (null model)
  ∧ LoopStep model n₁ n₂ mem₁
