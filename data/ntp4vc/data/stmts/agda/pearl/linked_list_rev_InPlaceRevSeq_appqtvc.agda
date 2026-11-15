-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linked_list_rev_InPlaceRevSeq_appqtvc: the linked-list append
-- verification condition for traversing the first list segment and linking
-- its final node to the second segment. This file contains no proof.

{-# OPTIONS --safe #-}

module linked_list_rev_InPlaceRevSeq_appqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _<N_ _≢_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_
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

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

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

_<N_ : Nat → Nat → Set
m <N n = natLess m n ≡ true

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

record LinkedListModel : Set₁ where
  field
    Loc       : Set
    locDefault : Loc
    null      : Loc
    eqLoc     : Loc → Loc → Bool
    eqLocSpec :
      (x y : Loc) →
      (eqLoc x y ≡ true) ↔ (x ≡ y)

open LinkedListModel

nthLoc :
  (model : LinkedListModel) →
  List (Loc model) →
  Int →
  Loc model
nthLoc model xs index =
  nthDefault (locDefault model) (toNat index) xs

update :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  Loc model →
  Loc model →
  Loc model
update model old key value query with eqLoc model query key
... | true = value
... | false = old query

disjoint :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  Set
disjoint model firstList secondList =
  (i₁ : Int) →
  (zeroZ ≤Z i₁ ∧ i₁ <Z lengthZ firstList) →
  (i₂ : Int) →
  (zeroZ ≤Z i₂ ∧ i₂ <Z lengthZ secondList) →
  nthLoc model firstList i₁ ≢ nthLoc model secondList i₂

listSeg :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  Set
listSeg model next₁ p s q =
  let n = lengthZ s
  in
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z n) →
    nthLoc model s i ≢ null model)
  ∧
  ((p ≡ q ∧ n ≡ zeroZ)
   ∨
   (oneZ ≤Z n
    ∧ nthLoc model s zeroZ ≡ p
    ∧ next₁ (nthLoc model s (subtractInt n oneZ)) ≡ q
    ∧
    ((i : Int) →
      (zeroZ ≤Z i ∧ i <Z subtractInt n oneZ) →
      next₁ (nthLoc model s i) ≡
        nthLoc model s (addInt i oneZ))))

InitialElseState :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Set
InitialElseState model next₁ l₁ l₁M =
  l₁ ≢ null model
  ∧ listSeg model next₁ l₁ [] l₁
  ∧ listSeg model next₁ l₁ l₁M (null model)
  ∧ ([] ++ l₁M) ≡ l₁M
  ∧ disjoint model [] l₁M

AdvanceConclusion :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Set
AdvanceConclusion model next₁ l₁ l₁M pM p o₈ =
  p ≢ null model
  ∧ (zeroZ ≤Z lengthZ pM ∧ length (drop (suc zero) pM) <N length pM)
  ∧ next₁ p ≢ null model
  ∧ listSeg model next₁ l₁ o₈ (next₁ p)
  ∧ listSeg model next₁ (next₁ p) (drop (suc zero) pM) (null model)
  ∧ (o₈ ++ drop (suc zero) pM) ≡ l₁M
  ∧ disjoint model o₈ (drop (suc zero) pM)

AppendObligation :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Set
AppendObligation model next₁ l₁ l₁M l₁pM pM p o₇ =
  let o₈ = l₁pM ++ o₇
  in
  (lengthZ o₈ ≡ addInt (lengthZ l₁pM) (lengthZ o₇)
   ∧
   ((i : Int) →
     (zeroZ ≤Z i ∧ i <Z lengthZ l₁pM) →
     nthLoc model o₈ i ≡ nthLoc model l₁pM i)
   ∧
   ((i : Int) →
     (lengthZ l₁pM ≤Z i ∧ i <Z lengthZ o₈) →
     nthLoc model o₈ i ≡
       nthLoc model o₇ (subtractInt i (lengthZ l₁pM))))
  →
  AdvanceConclusion model next₁ l₁ l₁M pM p o₈

SingletonObligation :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Set
SingletonObligation model next₁ l₁ l₁M l₁pM pM p =
  let o₆ : List (Loc model)
      o₆ = []
      o₇ = p ∷ o₆
  in
  (lengthZ o₇ ≡ addInt oneZ (lengthZ o₆)
   ∧ nthLoc model o₇ zeroZ ≡ p
   ∧
   ((i : Int) →
     (zeroZ <Z i ∧ i ≤Z lengthZ o₆) →
     nthLoc model o₇ i ≡
       nthLoc model o₆ (subtractInt i oneZ)))
  →
  AppendObligation model next₁ l₁ l₁M l₁pM pM p o₇

AdvanceBranch :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Set
AdvanceBranch model next₁ l₁ l₁M l₁pM pM p =
  (zeroZ ≤Z oneZ ∧ oneZ ≤Z lengthZ pM)
  ∧ SingletonObligation model next₁ l₁ l₁M l₁pM pM p

InnerCase :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Set
InnerCase model next₁ l₁ l₁M l₂ l₂M l₁pM pM p =
  p ≢ null model
  ∧
  (((eqLoc model (next₁ p) (null model) ≡ true)
      ↔ (next₁ p ≡ null model))
   →
   IfSet
     (notBool (eqLoc model (next₁ p) (null model)))
     (AdvanceBranch model next₁ l₁ l₁M l₁pM pM p)
     (p ≢ null model
      ∧ listSeg
          model
          (update model next₁ p l₂)
          l₁
          (l₁M ++ l₂M)
          (null model)))

DecompositionCases :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Set
DecompositionCases model next₁ l₁ l₁M l₂ l₂M =
  (l₁pM pM : List (Loc model)) →
  (p : Loc model) →
  (p ≢ null model
   ∧ listSeg model next₁ l₁ l₁pM p
   ∧ listSeg model next₁ p pM (null model)
   ∧ (l₁pM ++ pM) ≡ l₁M
   ∧ disjoint model l₁pM pM)
  →
  InnerCase model next₁ l₁ l₁M l₂ l₂M l₁pM pM p

AppConclusion :
  (model : LinkedListModel) →
  (Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Set
AppConclusion model next₁ l₁ l₁M l₂ l₂M =
  ((eqLoc model l₁ (null model) ≡ true) ↔ (l₁ ≡ null model))
  →
  IfSet
    (eqLoc model l₁ (null model))
    (listSeg model next₁ l₂ (l₁M ++ l₂M) (null model))
    (InitialElseState model next₁ l₁ l₁M
     ∧ DecompositionCases model next₁ l₁ l₁M l₂ l₂M)

app'vc : Set₁
app'vc =
  (model : LinkedListModel) →
  (next₁ : Loc model → Loc model) →
  (l₁ : Loc model) →
  (l₁M : List (Loc model)) →
  (l₂ : Loc model) →
  (l₂M : List (Loc model)) →
  listSeg model next₁ l₁ l₁M (null model) →
  listSeg model next₁ l₂ l₂M (null model) →
  disjoint model l₁M l₂M →
  AppConclusion model next₁ l₁ l₁M l₂ l₂M
