-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/vstte12_bfs_BFS_bfsqtvc: the breadth-first-search verification
-- condition for initialization, layer invariants, vertex processing,
-- successful discovery, and exhaustion of all reachable paths.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module vstte12_bfs_BFS_bfsqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _≢_
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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

contains : {A : Set} → DecEq A → A → List A → Bool
contains dec x [] = false
contains dec x (y ∷ ys) with dec x y
... | yes _ = true
... | no _ = contains dec x ys

removeAll : {A : Set} → DecEq A → A → List A → List A
removeAll dec x [] = []
removeAll dec x (y ∷ ys) with dec x y
... | yes _ = removeAll dec x ys
... | no _ = y ∷ removeAll dec x ys

nub : {A : Set} → DecEq A → List A → List A
nub dec [] = []
nub dec (x ∷ xs) with contains dec x xs
... | true = nub dec xs
... | false = x ∷ nub dec xs

record FSet (A : Set) : Set where
  constructor fset
  field
    elements : List A

open FSet

empty : {A : Set} → FSet A
empty = fset []

member : {A : Set} → DecEq A → A → FSet A → Set
member dec x set = contains dec x (elements set) ≡ true

notMember : {A : Set} → DecEq A → A → FSet A → Set
notMember dec x set = Not (member dec x set)

subset : {A : Set} → DecEq A → FSet A → FSet A → Set
subset {A = A} dec leftSet rightSet =
  (x : A) → member dec x leftSet → member dec x rightSet

setEqual : {A : Set} → DecEq A → FSet A → FSet A → Set
setEqual dec leftSet rightSet =
  subset dec leftSet rightSet ∧ subset dec rightSet leftSet

insert : {A : Set} → DecEq A → A → FSet A → FSet A
insert dec x set with contains dec x (elements set)
... | true = set
... | false = fset (x ∷ elements set)

erase : {A : Set} → DecEq A → A → FSet A → FSet A
erase dec x set = fset (removeAll dec x (elements set))

card : {A : Set} → DecEq A → FSet A → Nat
card dec set = length (nub dec (elements set))

module BFSTheory
  (Vertex : Set)
  (vertexDefault : Vertex)
  (successors : Vertex → FSet Vertex)
  (eqVertex : Vertex → Vertex → Set)
  (SetCarrier : Set)
  (setDefault : SetCarrier)
  (toFSet : SetCarrier → FSet Vertex)
  (choose : SetCarrier → Vertex)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  vertexDecEq : DecEq Vertex
  vertexDecEq x y = decide (x ≡ y)

  IfDec : {P : Set} → Dec P → Set → Set → Set
  IfDec (yes _) when-true when-false = when-true
  IfDec (no _) when-true when-false = when-false

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false =
    IfDec (decide P) when-true when-false

  Empty : FSet Vertex → Set
  Empty set = setEqual vertexDecEq set empty

  Nonempty : FSet Vertex → Set
  Nonempty set = Not (Empty set)

  record Laws : Set where
    field
      eqSpec :
        (x y : Vertex) →
        eqVertex x y ↔ x ≡ y

      chooseSpec :
        (set : SetCarrier) →
        Nonempty (toFSet set) →
        member vertexDecEq (choose set) (toFSet set)

  data Path : Vertex → Vertex → Int → Set where
    pathEmpty :
      (v : Vertex) →
      Path v v zeroZ

    pathSuccessor :
      (v₁ v₂ : Vertex) →
      (n : Int) →
      (v₃ : Vertex) →
      Path v₁ v₂ n →
      member vertexDecEq v₃ (successors v₂) →
      Path v₁ v₃ (addInt n oneZ)

  ShortestPath : Vertex → Vertex → Int → Set
  ShortestPath v₁ v₂ n =
    Path v₁ v₂ n ∧
    ((m : Int) →
      m <Z n →
      Not (Path v₁ v₂ m))

  Inv :
    Vertex →
    Vertex →
    FSet Vertex →
    FSet Vertex →
    FSet Vertex →
    Int →
    Set
  Inv source target visited current next distance =
    subset vertexDecEq current visited ∧
    ((x : Vertex) →
      member vertexDecEq x current →
      ShortestPath source x distance) ∧
    subset vertexDecEq next visited ∧
    ((x : Vertex) →
      member vertexDecEq x next →
      ShortestPath source x (addInt distance oneZ)) ∧
    ((x : Vertex) →
      (m : Int) →
      Path source x m →
      m ≤Z distance →
      member vertexDecEq x visited) ∧
    ((x : Vertex) →
      member vertexDecEq x visited →
      Exists Int λ m →
        Path source x m ∧
        m ≤Z addInt distance oneZ) ∧
    ((x : Vertex) →
      ShortestPath source x (addInt distance oneZ) →
      member vertexDecEq x next ∨
      notMember vertexDecEq x visited) ∧
    (member vertexDecEq target visited →
     member vertexDecEq target current ∨
     member vertexDecEq target next)

  Closure :
    FSet Vertex →
    FSet Vertex →
    FSet Vertex →
    Vertex →
    Set
  Closure visited current next x =
    member vertexDecEq x visited →
    notMember vertexDecEq x current →
    notMember vertexDecEq x next →
    (y : Vertex) →
    member vertexDecEq y (successors x) →
    member vertexDecEq y visited

  LayerInvariant :
    Vertex →
    Vertex →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    Int →
    Set
  LayerInvariant source target visited current next distance =
    Inv source target
      (toFSet visited) (toFSet current) (toFSet next) distance ∧
    (Empty (toFSet current) → Empty (toFSet next)) ∧
    ((x : Vertex) →
      Closure (toFSet visited) (toFSet current) (toFSet next) x) ∧
    zeroZ ≤Z distance

  AdvanceLayer :
    Vertex →
    Vertex →
    Int →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    Set
  AdvanceLayer source target distance visited current next =
    IfProp
      (Empty (toFSet current))
      ((freshNext : SetCarrier) →
       (Empty (toFSet freshNext) ∧
        natToInt (card vertexDecEq (toFSet freshNext)) ≡ zeroZ) →
       LayerInvariant
         source target visited next freshNext
         (addInt distance oneZ))
      (LayerInvariant source target visited current next distance)

  AfterFill :
    Vertex →
    Vertex →
    Int →
    Vertex →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    Set
  AfterFill source target distance v current visited next =
    Inv source target
      (toFSet visited) (toFSet current) (toFSet next) distance ∧
    subset vertexDecEq (successors v) (toFSet visited) ∧
    ((x : Vertex) →
      Closure (toFSet visited) (toFSet current) (toFSet next) x) →
    AdvanceLayer source target distance visited current next

  ProcessCurrent :
    Vertex →
    Vertex →
    Int →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    Set
  ProcessCurrent
    source target distance visited current next remaining =
    let v = choose current
    in
    (member vertexDecEq v (toFSet current) ∧
     setEqual vertexDecEq
       (toFSet remaining)
       (erase vertexDecEq v (toFSet current))) →
    (eqVertex v target ↔ v ≡ target) →
    IfProp
      (eqVertex v target)
      (ShortestPath source target distance)
      ((Inv source target
          (toFSet visited) (toFSet remaining) (toFSet next) distance ∧
        ShortestPath source v distance ∧
        ((x : Vertex) →
          x ≢ v →
          Closure
            (toFSet visited) (toFSet remaining) (toFSet next) x)) ∧
       ((next₁ visited₁ : SetCarrier) →
        AfterFill
          source target distance v remaining visited₁ next₁))

  LoopStep :
    Vertex →
    Vertex →
    Int →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    Set
  LoopStep source target distance visited current next =
    IfProp
      (Nonempty (toFSet current))
      (Nonempty (toFSet current) ∧
       ((remaining : SetCarrier) →
        ProcessCurrent
          source target distance visited current next remaining))
      ((distance₁ : Int) →
       Not (Path source target distance₁))

  LoopVerificationCondition : Vertex → Vertex → Set
  LoopVerificationCondition source target =
    (distance : Int) →
    (next current visited : SetCarrier) →
    LayerInvariant source target visited current next distance →
    LoopStep source target distance visited current next

  bfs-vc : Laws → Set
  bfs-vc laws =
    (visited o₁ o₂ visited₁ : SetCarrier) →
    (source : Vertex) →
    (current : SetCarrier) →
    (target : Vertex) →
    Empty (toFSet visited) →
    natToInt (card vertexDecEq (toFSet visited)) ≡ zeroZ →
    Empty (toFSet o₁) →
    natToInt (card vertexDecEq (toFSet o₁)) ≡ zeroZ →
    Empty (toFSet o₂) →
    natToInt (card vertexDecEq (toFSet o₂)) ≡ zeroZ →
    setEqual vertexDecEq
      (toFSet visited₁)
      (insert vertexDecEq source (toFSet visited)) →
    IfProp
      (member vertexDecEq source (toFSet visited))
      (card vertexDecEq (toFSet visited₁) ≡
       card vertexDecEq (toFSet visited))
      (natToInt (card vertexDecEq (toFSet visited₁)) ≡
       addInt
         (natToInt (card vertexDecEq (toFSet visited)))
         oneZ) →
    setEqual vertexDecEq
      (toFSet current)
      (insert vertexDecEq source (toFSet o₁)) →
    IfProp
      (member vertexDecEq source (toFSet o₁))
      (card vertexDecEq (toFSet current) ≡
       card vertexDecEq (toFSet o₁))
      (natToInt (card vertexDecEq (toFSet current)) ≡
       addInt
         (natToInt (card vertexDecEq (toFSet o₁)))
         oneZ) →
    LayerInvariant source target visited₁ current o₂ zeroZ ∧
    LoopVerificationCondition source target
