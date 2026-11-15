-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/list_removal_Top_remove1qtvc: the verification condition for removing
-- the first occurrence of an entry from a linked list by updating its
-- predecessor pointer. This file contains no proof.

{-# OPTIONS --safe #-}

module list_removal_Top_remove1qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

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

InitialState :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Loc model →
  Set
InitialState model n₁ n₂ mem₁ o₂ =
  (zeroZ <Z oneZ ∧ oneZ ≤Z n₁)
  ∧ list model mem₁ (head model) oneZ o₂
  ∧ o₂ ≢ null model
  ∧ list model mem₁ o₂ (subtractInt n₁ oneZ) (entry model)
  ∧ list model mem₁ (entry model) n₂ (null model)

AdvanceBranch :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Int →
  Loc model →
  Set
AdvanceBranch model n₁ n₂ mem₁ n curr =
  curr ≢ null model
  ∧
  (zeroZ ≤Z subtractInt n₁ n
   ∧ subtractInt n₁ (addInt n oneZ) <Z subtractInt n₁ n)
  ∧
  (zeroZ <Z addInt n oneZ ∧ addInt n oneZ ≤Z n₁)
  ∧ list model mem₁
      (head model)
      (addInt n oneZ)
      (mem₁ curr)
  ∧ mem₁ curr ≢ null model
  ∧ (curr ≡ null model → addInt n oneZ ≡ oneZ)
  ∧ (curr ≢ null model → ⊤)
  ∧ (curr ≢ null model →
      list model mem₁
        (head model)
        (subtractInt (addInt n oneZ) oneZ)
        curr)
  ∧ list model mem₁
      (mem₁ curr)
      (subtractInt n₁ (addInt n oneZ))
      (entry model)
  ∧ list model mem₁ (entry model) n₂ (null model)

RemoveHeadBranch :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Loc model →
  Set
RemoveHeadBranch model n₁ n₂ mem₁ curr =
  curr ≢ null model
  ∧
  let o₃ = head model
  in
  o₃ ≢ null model
  ∧ list model
      (update model mem₁ o₃ (mem₁ curr))
      (head model)
      (subtractInt (addInt n₁ n₂) oneZ)
      (null model)

RemoveAfterPredecessorBranch :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Loc model →
  Loc model →
  Set
RemoveAfterPredecessorBranch model n₁ n₂ mem₁ curr prev =
  curr ≢ null model
  ∧ prev ≢ null model
  ∧ list model
      (update model mem₁ prev (mem₁ curr))
      (head model)
      (subtractInt (addInt n₁ n₂) oneZ)
      (null model)

LoopStepConclusion :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Int →
  Loc model →
  Loc model →
  Set
LoopStepConclusion model n₁ n₂ mem₁ n curr prev =
  IfSet
    (notBool (eqLoc model curr (entry model)))
    (AdvanceBranch model n₁ n₂ mem₁ n curr)
    (IfSet
      (eqLoc model prev (null model))
      (RemoveHeadBranch model n₁ n₂ mem₁ curr)
      (RemoveAfterPredecessorBranch model n₁ n₂ mem₁ curr prev))

LoopStep :
  (model : ListRemovalModel) →
  Int →
  Int →
  (Loc model → Loc model) →
  Set
LoopStep model n₁ n₂ mem₁ =
  (n : Int) →
  (curr prev : Loc model) →
  ((zeroZ <Z n ∧ n ≤Z n₁)
   ∧ list model mem₁ (head model) n curr
   ∧ curr ≢ null model
   ∧ (prev ≡ null model → n ≡ oneZ)
   ∧ (prev ≢ null model → mem₁ prev ≡ curr)
   ∧ (prev ≢ null model →
      list model mem₁
        (head model)
        (subtractInt n oneZ)
        prev)
   ∧ list model mem₁ curr (subtractInt n₁ n) (entry model)
   ∧ list model mem₁ (entry model) n₂ (null model))
  →
  LoopStepConclusion model n₁ n₂ mem₁ n curr prev

remove1'vc : Set₁
remove1'vc =
  (model : ListRemovalModel) →
  (n₁ n₂ : Int) →
  (mem₁ : Loc model → Loc model) →
  zeroZ <Z n₁ →
  zeroZ <Z n₂ →
  list model mem₁ (head model) n₁ (entry model) →
  list model mem₁ (entry model) n₂ (null model) →
  let o₁ = head model
      o₂ = mem₁ o₁
  in
  o₁ ≢ null model
  ∧ InitialState model n₁ n₂ mem₁ o₂
  ∧ LoopStep model n₁ n₂ mem₁
