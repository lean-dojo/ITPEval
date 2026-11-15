-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linked_list_rev_InPlaceRevSeq_in_place_reverseqtvc: the in-place
-- linked-list reversal verification condition, including its loop invariant
-- and the pointer-update branch obligation. This file contains no proof.

{-# OPTIONS --safe #-}

module LinkedListRevInPlaceReverseVC where

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

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

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
    Loc        : Set
    locDefault : Loc
    null       : Loc
    eqLoc      : Loc → Loc → Bool
    eqLocSpec  :
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

UpdatedConclusion :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  List (Loc model) →
  Set
UpdatedConclusion model original pM p r next₂ accumulated =
  (zeroZ ≤Z oneZ ∧ oneZ ≤Z lengthZ pM)
  ∧
  (zeroZ ≤Z lengthZ pM
   ∧ length (drop (suc zero) pM) <N length pM)
  ∧
  listSeg
    model
    (update model next₂ p r)
    (next₂ p)
    (drop (suc zero) pM)
    (null model)
  ∧
  listSeg
    model
    (update model next₂ p r)
    p
    accumulated
    (null model)
  ∧
  disjoint model (drop (suc zero) pM) accumulated
  ∧
  (reverse (drop (suc zero) pM) ++ accumulated) ≡ reverse original

ConsStepObligation :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  Set
ConsStepObligation model original rM pM p r next₂ =
  let oldHead = nthLoc model pM zeroZ
      accumulated = oldHead ∷ rM
  in
  (lengthZ accumulated ≡ addInt oneZ (lengthZ rM)
   ∧ nthLoc model accumulated zeroZ ≡ oldHead
   ∧
   ((i : Int) →
     (zeroZ <Z i ∧ i ≤Z lengthZ rM) →
     nthLoc model accumulated i ≡
       nthLoc model rM (subtractInt i oneZ)))
  →
  UpdatedConclusion model original pM p r next₂ accumulated

NonNullBranch :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  Set
NonNullBranch model original rM pM p r next₂ =
  p ≢ null model
  ∧ p ≢ null model
  ∧ ConsStepObligation model original rM pM p r next₂

LoopBodyConclusion :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  (Loc model → Loc model) →
  Set
LoopBodyConclusion model original rM r pM p next₂ =
  let o₁ = null model
      o₂ = eqLoc model p o₁
  in
  ((o₂ ≡ true) ↔ (p ≡ o₁))
  →
  IfSet
    (notBool o₂)
    (NonNullBranch model original rM pM p r next₂)
    (listSeg model next₂ r (reverse original) (null model))

LoopObligation :
  (model : LinkedListModel) →
  List (Loc model) →
  Set
LoopObligation model original =
  (rM : List (Loc model)) →
  (r : Loc model) →
  (pM : List (Loc model)) →
  (p : Loc model) →
  (next₂ : Loc model → Loc model) →
  (listSeg model next₂ p pM (null model)
   ∧ listSeg model next₂ r rM (null model)
   ∧ disjoint model pM rM
   ∧ (reverse pM ++ rM) ≡ reverse original)
  →
  LoopBodyConclusion model original rM r pM p next₂

in-place-reverse'vc : Set₁
in-place-reverse'vc =
  (model : LinkedListModel) →
  (next₁ : Loc model → Loc model) →
  (l : Loc model) →
  (lM : List (Loc model)) →
  listSeg model next₁ l lM (null model) →
  listSeg model next₁ l lM (null model)
  ∧ listSeg model next₁ (null model) [] (null model)
  ∧ disjoint model lM []
  ∧ (reverse lM ++ []) ≡ reverse lM
  ∧ LoopObligation model lM
