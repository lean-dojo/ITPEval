-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linked_list_rev_InPlaceRev_in_place_reverseqtvc: the in-place
-- linked-list reversal verification condition, including its loop invariant
-- and pointer-update branch. This file contains no proof.

{-# OPTIONS --safe #-}

module LinkedListRevInPlaceReverseInductiveVC where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)

infix 4 _∈_ _≢_
infixr 5 _++_
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

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

record LinkedListModel : Set₁ where
  field
    Loc       : Set
    null      : Loc
    eqLoc     : Loc → Loc → Bool
    eqLocSpec :
      (x y : Loc) →
      (eqLoc x y ≡ true) ↔ (x ≡ y)

open LinkedListModel

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
  (x : Loc model) →
  Not (x ∈ firstList ∧ x ∈ secondList)

noRepet :
  (model : LinkedListModel) →
  List (Loc model) →
  Set
noRepet model [] = ⊤
noRepet model (x ∷ rest) =
  Not (x ∈ rest) ∧ noRepet model rest

data ListSeg
  (model : LinkedListModel)
  (next : Loc model → Loc model) :
  Loc model →
  List (Loc model) →
  Loc model →
  Set where

  listSegNil :
    (p : Loc model) →
    ListSeg model next p [] p

  listSegCons :
    (p : Loc model) →
    (segment : List (Loc model)) →
    (q : Loc model) →
    p ≢ null model →
    ListSeg model next (next p) segment q →
    ListSeg model next p (p ∷ segment) q

MatchedTail :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  List (Loc model) →
  Set
MatchedTail model original rM r p next₁ [] = ⊥
MatchedTail model original rM r p next₁ (h ∷ t) =
  t ≡ t
  ∧ ListSeg
      model
      (update model next₁ p r)
      (next₁ p)
      t
      (null model)
  ∧ ListSeg
      model
      (update model next₁ p r)
      p
      (h ∷ rM)
      (null model)
  ∧ disjoint model t (h ∷ rM)
  ∧ (reverse t ++ (h ∷ rM)) ≡ reverse original

NonNullBranch :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Loc model →
  (Loc model → Loc model) →
  List (Loc model) →
  Set
NonNullBranch model original rM r p next₁ pM =
  p ≢ null model
  ∧ MatchedTail model original rM r p next₁ pM

LoopBodyConclusion :
  (model : LinkedListModel) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  (Loc model → Loc model) →
  Set
LoopBodyConclusion model original rM r pM p next₁ =
  let o₁ = null model
      o₂ = eqLoc model p o₁
  in
  ((o₂ ≡ true) ↔ (p ≡ o₁))
  →
  IfSet
    (notBool o₂)
    (NonNullBranch model original rM r p next₁ pM)
    (ListSeg model next₁ r (reverse original) (null model))

LoopObligation :
  (model : LinkedListModel) →
  List (Loc model) →
  Set
LoopObligation model original =
  (rM : List (Loc model)) →
  (r : Loc model) →
  (pM : List (Loc model)) →
  (p : Loc model) →
  (next₁ : Loc model → Loc model) →
  (ListSeg model next₁ p pM (null model)
   ∧ ListSeg model next₁ r rM (null model)
   ∧ disjoint model pM rM
   ∧ (reverse pM ++ rM) ≡ reverse original)
  →
  LoopBodyConclusion model original rM r pM p next₁

in-place-reverse'vc : Set₁
in-place-reverse'vc =
  (model : LinkedListModel) →
  (l : Loc model) →
  (next : Loc model → Loc model) →
  (lM : List (Loc model)) →
  ListSeg model next l lM (null model) →
  ListSeg model next l lM (null model)
  ∧ ListSeg model next (null model) [] (null model)
  ∧ disjoint model lM []
  ∧ (reverse lM ++ []) ≡ reverse lM
  ∧ LoopObligation model lM
