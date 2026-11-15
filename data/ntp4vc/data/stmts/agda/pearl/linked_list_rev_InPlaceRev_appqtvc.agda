-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linked_list_rev_InPlaceRev_appqtvc: the linked-list append
-- verification condition for traversing the first list segment and linking
-- its final node to the second segment. This file contains no proof.

{-# OPTIONS --safe #-}

module linked_list_rev_InPlaceRev_appqtvc where

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

InitialElseState :
  (model : LinkedListModel) →
  (next : Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Set
InitialElseState model next l₁ l₁M =
  l₁ ≢ null model
  ∧ ListSeg model next l₁ [] l₁
  ∧ ListSeg model next l₁ l₁M (null model)
  ∧ ([] ++ l₁M) ≡ l₁M
  ∧ disjoint model [] l₁M

AdvanceBranch :
  (model : LinkedListModel) →
  (next : Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Set
AdvanceBranch model next l₁ l₁M l₁pM [] p = ⊥
AdvanceBranch model next l₁ l₁M l₁pM (h ∷ t) p =
  p ≢ null model
  ∧ t ≡ t
  ∧ next p ≢ null model
  ∧ ListSeg
      model
      next
      l₁
      (l₁pM ++ (h ∷ []))
      (next p)
  ∧ ListSeg model next (next p) t (null model)
  ∧ ((l₁pM ++ (h ∷ [])) ++ t) ≡ l₁M
  ∧ disjoint model (l₁pM ++ (h ∷ [])) t

InnerCase :
  (model : LinkedListModel) →
  (next : Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  List (Loc model) →
  List (Loc model) →
  Loc model →
  Set
InnerCase model next l₁ l₁M l₂ l₂M l₁pM pM p =
  p ≢ null model
  ∧
  (((eqLoc model (next p) (null model) ≡ true)
      ↔ (next p ≡ null model))
   →
   IfSet
     (notBool (eqLoc model (next p) (null model)))
     (AdvanceBranch model next l₁ l₁M l₁pM pM p)
     (p ≢ null model
      ∧ ListSeg
          model
          (update model next p l₂)
          l₁
          (l₁M ++ l₂M)
          (null model)))

DecompositionCases :
  (model : LinkedListModel) →
  (next : Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Set
DecompositionCases model next l₁ l₁M l₂ l₂M =
  (l₁pM pM : List (Loc model)) →
  (p : Loc model) →
  (p ≢ null model
   ∧ ListSeg model next l₁ l₁pM p
   ∧ ListSeg model next p pM (null model)
   ∧ (l₁pM ++ pM) ≡ l₁M
   ∧ disjoint model l₁pM pM)
  →
  InnerCase model next l₁ l₁M l₂ l₂M l₁pM pM p

AppConclusion :
  (model : LinkedListModel) →
  (next : Loc model → Loc model) →
  Loc model →
  List (Loc model) →
  Loc model →
  List (Loc model) →
  Set
AppConclusion model next l₁ l₁M l₂ l₂M =
  ((eqLoc model l₁ (null model) ≡ true) ↔ (l₁ ≡ null model))
  →
  IfSet
    (eqLoc model l₁ (null model))
    (ListSeg model next l₂ (l₁M ++ l₂M) (null model))
    (InitialElseState model next l₁ l₁M
     ∧ DecompositionCases model next l₁ l₁M l₂ l₂M)

app'vc : Set₁
app'vc =
  (model : LinkedListModel) →
  (l₁ : Loc model) →
  (next : Loc model → Loc model) →
  (l₁M : List (Loc model)) →
  (l₂ : Loc model) →
  (l₂M : List (Loc model)) →
  ListSeg model next l₁ l₁M (null model) →
  ListSeg model next l₂ l₂M (null model) →
  disjoint model l₁M l₂M →
  AppConclusion model next l₁ l₁M l₂ l₂M
