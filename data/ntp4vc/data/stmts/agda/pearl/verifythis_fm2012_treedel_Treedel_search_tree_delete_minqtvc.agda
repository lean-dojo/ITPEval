-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc:
-- the verification condition for deleting the minimum node of a pointer-based
-- binary search tree by left descent and zipper reconstruction. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.List using (List; []; _∷_)

infix 4 _∈_ _∉_ _≢_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊤ : Set where
  tt : ⊤

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

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

_∉_ : {A : Set} → A → List A → Set
x ∉ xs = Not (x ∈ xs)

NoDup : {A : Set} → List A → Set
NoDup [] = ⊤
NoDup (x ∷ xs) = x ∉ xs ∧ NoDup xs

record TreeDelModel : Set₁ where
  field
    Loc       : Set
    null      : Loc
    eqLoc     : Loc → Loc → Bool
    eqLocSpec :
      (x y : Loc) →
      (eqLoc x y ≡ true) ↔ (x ≡ y)

module TreeDelTheory (model : TreeDelModel) where

  open TreeDelModel model

  record NodeData : Set where
    constructor node
    field
      left1    : Loc
      right1   : Loc
      nodeData : Int

  open NodeData

  Memory : Set
  Memory = Loc → NodeData

  data Tree (A : Set) : Set where
    Empty : Tree A
    Node  : Tree A → A → Tree A → Tree A

  root : Tree Loc → Loc
  root Empty = null
  root (Node l p r) = p

  istree : Memory → Tree Loc → Set
  istree mem Empty = ⊤
  istree mem (Node l p r) =
    p ≢ null
    ∧ istree mem l
    ∧ istree mem r
    ∧ root l ≡ left1 (mem p)
    ∧ root r ≡ right1 (mem p)

  inorder : {A : Set} → Tree A → List A
  inorder Empty = []
  inorder (Node l x r) = inorder l ++ (x ∷ inorder r)

  data Zipper (A : Set) : Set where
    Top  : Zipper A
    Left : Zipper A → A → Tree A → Zipper A

  zip : {A : Set} → Tree A → Zipper A → Tree A
  zip t Top = t
  zip t (Left z x r) = zip (Node t x r) z

  inorderz : {A : Set} → Zipper A → List A
  inorderz Top = []
  inorderz (Left z x r) = x ∷ inorder r ++ inorderz z

  eqSpec : Loc → Loc → Set
  eqSpec x y = (eqLoc x y ≡ true) ↔ (x ≡ y)

  rightChild : Tree Loc → Tree Loc → Set
  rightChild Empty child = ⊥
  rightChild (Node l p r) child = child ≡ r

  leftChild : Tree Loc → Tree Loc → Set
  leftChild Empty child = ⊥
  leftChild (Node l p r) child = child ≡ l

  isEitherChild : Tree Loc → Tree Loc → Set
  isEitherChild Empty child = ⊥
  isEitherChild (Node l p r) child = l ≡ child ∨ r ≡ child

  rootDataConclusion :
    Memory → Tree Loc → Tree Loc → Set
  rootDataConclusion mem it r with inorder it
  ... | [] = ⊥
  ... | p ∷ l =
    nodeData (mem (root it)) ≡ nodeData (mem p)
    ∧ inorder r ≡ l

  rootDeletionBranch : Memory → Tree Loc → Set
  rootDeletionBranch mem Empty = ⊥
  rootDeletionBranch mem (Node l p r) =
    istree mem r
    ∧ root r ≡ right1 (mem (root (Node l p r)))
    ∧ rootDataConclusion mem (Node l p r) r

  immediateLeftBranch : Memory → Tree Loc → Set
  immediateLeftBranch mem it =
    root it ≢ null
    ∧ root it ≢ null
    ∧ rootDeletionBranch mem it

  finalInorderConclusion :
    Tree Loc → Memory → Memory → Loc → Tree Loc → Set
  finalInorderConclusion it mem mem1 pp rebuilt with inorder it
  ... | [] = ⊥
  ... | p ∷ l =
    nodeData (mem (left1 (mem pp))) ≡ nodeData (mem1 p)
    ∧ inorder rebuilt ≡ l

  updatedNode : Memory → Loc → NodeData
  updatedNode mem pp =
    let old = mem pp
    in
    node
      (right1 (mem (left1 (mem pp))))
      (right1 old)
      (nodeData old)

  memoryUpdatePremise : Memory → Memory → Loc → Set
  memoryUpdatePremise mem mem1 pp =
    mem1 pp ≡ updatedNode mem pp
    ∧ ((q : Loc) → q ≢ pp → mem1 q ≡ mem q)

  allDataUnchanged : Memory → Memory → Set
  allDataUnchanged mem mem1 =
    (p : Loc) → nodeData (mem1 p) ≡ nodeData (mem p)

  updatedMemoryConclusion :
    Tree Loc →
    Memory →
    Tree Loc →
    Tree Loc →
    Zipper Loc →
    Loc →
    Memory →
    Set
  updatedMemoryConclusion it mem subtree ppr zipper1 pp mem1 =
    subtree ≢ Empty
    ∧ ((pl : Tree Loc) →
      leftChild subtree pl →
      subtree ≢ Empty
      ∧ ((o6 : Tree Loc) →
        rightChild subtree o6 →
        let rebuilt = zip o6 (Left zipper1 pp ppr)
        in
        allDataUnchanged mem mem1
        ∧ istree mem1 rebuilt
        ∧ root rebuilt ≡ root it
        ∧ finalInorderConclusion it mem mem1 pp rebuilt))

  deepNullBranch :
    Tree Loc →
    Memory →
    Tree Loc →
    Tree Loc →
    Zipper Loc →
    Loc →
    Set
  deepNullBranch it mem subtree ppr zipper1 pp =
    left1 (mem pp) ≢ null
    ∧ left1 (mem pp) ≢ null
    ∧ pp ≢ null
    ∧ ((mem1 : Memory) →
      memoryUpdatePremise mem mem1 pp →
      updatedMemoryConclusion it mem subtree ppr zipper1 pp mem1)

  deepNonNullBranch :
    Tree Loc →
    Memory →
    Tree Loc →
    Tree Loc →
    Zipper Loc →
    Loc →
    Set
  deepNonNullBranch it mem subtree ppr zipper1 pp =
    subtree ≢ Empty
    ∧ ((o6 : Tree Loc) →
      rightChild subtree o6 →
      subtree ≢ Empty
      ∧ ((o7 : Tree Loc) →
        leftChild subtree o7 →
        let deeper = left1 (mem (left1 (mem pp)))
            rebuilt = Node o7 (left1 (mem pp)) o6
        in
        deeper ≢ null
        ∧ isEitherChild subtree o7
        ∧ left1 (mem pp) ≢ null
        ∧ deeper ≢ null
        ∧ istree mem rebuilt
        ∧ zip rebuilt (Left zipper1 pp ppr) ≡ it))

  loopBodyConclusion :
    Tree Loc →
    Memory →
    Tree Loc →
    Tree Loc →
    Zipper Loc →
    Loc →
    Set
  loopBodyConclusion it mem subtree ppr zipper1 pp =
    let deeper = left1 (mem (left1 (mem pp)))
        o5 = null
    in
    eqSpec deeper o5 →
    IfSet
      (notBool (eqLoc deeper o5))
      (deepNonNullBranch it mem subtree ppr zipper1 pp)
      (deepNullBranch it mem subtree ppr zipper1 pp)

  loopPremise :
    Tree Loc →
    Memory →
    Tree Loc →
    Tree Loc →
    Zipper Loc →
    Loc →
    Set
  loopPremise it mem subtree ppr zipper1 pp =
    pp ≢ null
    ∧ left1 (mem pp) ≢ null
    ∧ istree mem (Node subtree pp ppr)
    ∧ zip (Node subtree pp ppr) zipper1 ≡ it

  loopObligation : Tree Loc → Memory → Set
  loopObligation it mem =
    (subtree : Tree Loc) →
    (ppr : Tree Loc) →
    (zipper1 : Zipper Loc) →
    (pp : Loc) →
    loopPremise it mem subtree ppr zipper1 pp →
    loopBodyConclusion it mem subtree ppr zipper1 pp

  initialDescentConclusion :
    Tree Loc →
    Memory →
    Loc →
    Tree Loc →
    Tree Loc →
    Set
  initialDescentConclusion it mem o1 o3 o4 =
    ((root it ≢ null ∧ left1 (mem (root it)) ≡ o1)
     ∧ o1 ≢ null
     ∧ istree mem (Node o4 (root it) o3)
     ∧ zip (Node o4 (root it) o3) Top ≡ it)
    ∧ loopObligation it mem

  leftDescentBranch :
    Tree Loc → Memory → Loc → Set
  leftDescentBranch it mem o1 =
    o1 ≢ null
    ∧ it ≢ Empty
    ∧ ((o3 : Tree Loc) →
      rightChild it o3 →
      it ≢ Empty
      ∧ ((o4 : Tree Loc) →
        leftChild it o4 →
        initialDescentConclusion it mem o1 o3 o4))

  mainConclusion : Tree Loc → Memory → Set
  mainConclusion it mem =
    root it ≢ null
    ∧
    let o1 = left1 (mem (root it))
        o2 = null
    in
    eqSpec o1 o2 →
    IfSet
      (eqLoc o1 o2)
      (immediateLeftBranch mem it)
      (leftDescentBranch it mem o1)

  VC : Set
  VC =
    (it : Tree Loc) →
    (mem : Memory) →
    root it ≢ null →
    istree mem it →
    NoDup (inorder it) →
    mainConclusion it mem

search-tree-delete-min'vc : Set₁
search-tree-delete-min'vc =
  (model : TreeDelModel) →
  TreeDelTheory.VC model
