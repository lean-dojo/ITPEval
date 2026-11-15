-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/dijkstra_DijkstraShortestPath_shortest_path_codeqtvc: the Dijkstra
-- shortest-path verification condition for initialization, queue and
-- successor loops, invariants, variants, and final path optimality.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module dijkstra_DijkstraShortestPath_shortest_path_codeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _<N_ _≢_
infixr 3 _∧_
infixr 2 _∨_

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

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

DecEq : Set → Set
DecEq A = (x y : A) → Dec (x ≡ y)

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
x <N y = natLess x y ≡ true

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

module DijkstraTheory
  (Vertex : Set)
  (vertexDefault : Vertex)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (SetCarrier : Set)
  (setDefault : SetCarrier)
  (toFSet : SetCarrier → FSet Vertex)
  (choose : SetCarrier → Vertex)
  (Map : Set → Set)
  (mapDefault : {A : Set} → A → Map A)
  (contents : {A : Set} → Map A → Vertex → A)
  (create : {A : Set} → A → Map A)
  (lookup : {A : Set} → Map A → Vertex → A)
  (update : {A : Set} → Map A → Vertex → A → Map A)
  (vertices : FSet Vertex)
  (successors : Vertex → FSet Vertex)
  (weight : Vertex → Vertex → Int)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  vertexDecEq : DecEq Vertex
  vertexDecEq x y = decide (x ≡ y)

  updateValue :
    {A : Set} →
    (Vertex → A) →
    Vertex →
    A →
    Vertex →
    A
  updateValue old key value query with vertexDecEq query key
  ... | yes _ = value
  ... | no _ = old query

  EmptySet : FSet Vertex → Set
  EmptySet set = setEqual vertexDecEq set empty

  Nonempty : FSet Vertex → Set
  Nonempty set = Not (EmptySet set)

  IfDec : {P : Set} → Dec P → Set → Set → Set
  IfDec (yes _) when-true when-false = when-true
  IfDec (no _) when-true when-false = when-false

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false =
    IfDec (decide P) when-true when-false

  record Laws : Set₁ where
    field
      chooseSpec :
        (set : SetCarrier) →
        Nonempty (toFSet set) →
        member vertexDecEq (choose set) (toFSet set)

      createSpec :
        {A : Set} →
        (x : A) →
        (key : Vertex) →
        contents (create x) key ≡ x

      lookupSpec :
        {A : Set} →
        (map : Map A) →
        (key : Vertex) →
        lookup map key ≡ contents map key

      updateSpec :
        {A : Set} →
        (map : Map A) →
        (key : Vertex) →
        (value : A) →
        (query : Vertex) →
        contents (update map key value) query ≡
          updateValue (contents map) key value query

      successorsSpec :
        (x : Vertex) →
        subset vertexDecEq (successors x) vertices

      weightSpec :
        (x y : Vertex) →
        zeroZ ≤Z weight x y

  data Path : Vertex → Vertex → Int → Set where
    pathNil :
      (x : Vertex) →
      Path x x zeroZ

    pathCons :
      (x y : Vertex) →
      (distance : Int) →
      (z : Vertex) →
      Path x y distance →
      member vertexDecEq z (successors y) →
      Path x z (addInt distance (weight y z))

  Minimum : Vertex → SetCarrier → Map Int → Set
  Minimum m q d =
    member vertexDecEq m (toFSet q) ∧
    ((x : Vertex) →
      member vertexDecEq x (toFSet q) →
      lookup d m ≤Z lookup d x)

  ShortestPath : Vertex → Vertex → Int → Set
  ShortestPath x y distance =
    Path x y distance ∧
    ((otherDistance : Int) →
      Path x y otherDistance →
      distance ≤Z otherDistance)

  InvSource : Vertex → SetCarrier → SetCarrier → Set
  InvSource source settled queue =
    member vertexDecEq source (toFSet settled) ∨
    member vertexDecEq source (toFSet queue)

  Inv :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Set
  Inv source settled queue distances =
    InvSource source settled queue ∧
    lookup distances source ≡ zeroZ ∧
    subset vertexDecEq (toFSet settled) vertices ∧
    subset vertexDecEq (toFSet queue) vertices ∧
    ((v₁ : Vertex) →
      member vertexDecEq v₁ (toFSet queue) →
      notMember vertexDecEq v₁ (toFSet settled)) ∧
    ((v₁ : Vertex) →
      member vertexDecEq v₁ (toFSet settled) →
      ShortestPath source v₁ (lookup distances v₁)) ∧
    ((v₁ : Vertex) →
      member vertexDecEq v₁ (toFSet queue) →
      Path source v₁ (lookup distances v₁))

  InvSuccessors :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Set
  InvSuccessors source settled queue distances =
    (x : Vertex) →
    member vertexDecEq x (toFSet settled) →
    (y : Vertex) →
    member vertexDecEq y (successors x) →
    (member vertexDecEq y (toFSet settled) ∨
     member vertexDecEq y (toFSet queue)) ∧
    lookup distances y ≤Z
      addInt (lookup distances x) (weight x y)

  InvSuccessorsExcept :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Vertex →
    SetCarrier →
    Set
  InvSuccessorsExcept source settled queue distances u pending =
    (x : Vertex) →
    member vertexDecEq x (toFSet settled) →
    (y : Vertex) →
    member vertexDecEq y (successors x) →
    (x ≢ u ∨
     (x ≡ u ∧ notMember vertexDecEq y (toFSet pending))) →
    (member vertexDecEq y (toFSet settled) ∨
     member vertexDecEq y (toFSet queue)) ∧
    lookup distances y ≤Z
      addInt (lookup distances x) (weight x y)

  MinimumClosure :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Set
  MinimumClosure source settled queue distances =
    (m : Vertex) →
    Minimum m queue distances →
    (x : Vertex) →
    (dx : Int) →
    Path source x dx →
    dx <Z lookup distances m →
    member vertexDecEq x (toFSet settled)

  UpdateCase :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Vertex →
    SetCarrier →
    Map Int →
    Set
  UpdateCase u visited₂ queue₃ distances₂ v₁ queue₄ distances₃ =
    (member vertexDecEq v₁ (toFSet visited₂) ∧
     queue₄ ≡ queue₃ ∧
     distances₃ ≡ distances₂) ∨
    (member vertexDecEq v₁ (toFSet queue₄) ∧
     lookup distances₃ v₁ ≤Z
       addInt (lookup distances₃ u) (weight u v₁) ∧
     queue₄ ≡ queue₃ ∧
     distances₃ ≡ distances₂) ∨
    (member vertexDecEq v₁ (toFSet queue₄) ∧
     addInt (lookup distances₂ u) (weight u v₁) <Z
       lookup distances₂ v₁ ∧
     queue₄ ≡ queue₃ ∧
     distances₃ ≡
       update distances₂ v₁
         (addInt (lookup distances₂ u) (weight u v₁))) ∨
    (notMember vertexDecEq v₁ (toFSet visited₂) ∧
     notMember vertexDecEq v₁ (toFSet queue₃) ∧
     setEqual vertexDecEq
       (toFSet queue₄)
       (insert vertexDecEq v₁ (toFSet queue₃)) ∧
     distances₃ ≡
       update distances₂ v₁
         (addInt (lookup distances₂ u) (weight u v₁)))

  NeighborBranch :
    Vertex →
    SetCarrier →
    SetCarrier →
    SetCarrier →
    Map Int →
    Vertex →
    SetCarrier →
    Set
  NeighborBranch
    source visited₁ visited₂ queue₃ distances₂ u pending₁ =
    IfProp
      (Nonempty (toFSet pending₁))
      (Nonempty (toFSet pending₁) ∧
       ((pending₂ : SetCarrier) →
        let v₁ = choose pending₁
        in
        (member vertexDecEq v₁ (toFSet pending₁) ∧
         setEqual vertexDecEq
           (toFSet pending₂)
           (erase vertexDecEq v₁ (toFSet pending₁))) →
        (queue₄ : SetCarrier) →
        (distances₃ : Map Int) →
        UpdateCase
          u visited₂ queue₃ distances₂ v₁ queue₄ distances₃ →
        ((zeroZ ≤Z natToInt
            (card vertexDecEq (toFSet pending₁))) ∧
         (card vertexDecEq (toFSet pending₂) <N
          card vertexDecEq (toFSet pending₁))) ∧
        subset vertexDecEq (toFSet pending₂) (successors u) ∧
        Inv source visited₂ queue₄ distances₃ ∧
        InvSuccessorsExcept
          source visited₂ queue₄ distances₃ u pending₂))
      (((zeroZ ≤Z
          subtractInt
            (natToInt (card vertexDecEq vertices))
            (natToInt (card vertexDecEq (toFSet visited₁)))) ∧
        (subtractInt
           (natToInt (card vertexDecEq vertices))
           (natToInt (card vertexDecEq (toFSet visited₂))) <Z
         subtractInt
           (natToInt (card vertexDecEq vertices))
           (natToInt (card vertexDecEq (toFSet visited₁))))) ∧
       Inv source visited₂ queue₃ distances₂ ∧
       InvSuccessors source visited₂ queue₃ distances₂ ∧
       MinimumClosure source visited₂ queue₃ distances₂)

  SuccessorLoop :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Vertex →
    SetCarrier →
    SetCarrier →
    Set
  SuccessorLoop
    source visited₁ queue₂ distances₁ u visited₂ pending =
    (setEqual vertexDecEq (toFSet pending) (successors u)) →
    (subset vertexDecEq (toFSet pending) (successors u) ∧
     Inv source visited₂ queue₂ distances₁ ∧
     InvSuccessorsExcept
       source visited₂ queue₂ distances₁ u pending) ∧
    ((pending₁ : SetCarrier) →
     (queue₃ : SetCarrier) →
     (distances₂ : Map Int) →
     subset vertexDecEq (toFSet pending₁) (successors u) ∧
     Inv source visited₂ queue₃ distances₂ ∧
     InvSuccessorsExcept
       source visited₂ queue₃ distances₂ u pending₁ →
     NeighborBranch
       source visited₁ visited₂ queue₃ distances₂ u pending₁)

  QueueRemoval :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    SetCarrier →
    Vertex →
    Set
  QueueRemoval source visited₁ queue₁ distances₁ queue₂ u =
    Minimum u queue₁ distances₁ ∧
    setEqual vertexDecEq
      (toFSet queue₂)
      (erase vertexDecEq u (toFSet queue₁)) →
    (visited₂ : SetCarrier) →
    setEqual vertexDecEq
      (toFSet visited₂)
      (insert vertexDecEq u (toFSet visited₁)) ∧
    IfProp
      (member vertexDecEq u (toFSet visited₁))
      (card vertexDecEq (toFSet visited₂) ≡
       card vertexDecEq (toFSet visited₁))
      (natToInt (card vertexDecEq (toFSet visited₂)) ≡
       addInt
         (natToInt (card vertexDecEq (toFSet visited₁)))
         oneZ) →
    (pending : SetCarrier) →
    SuccessorLoop
      source visited₁ queue₂ distances₁ u visited₂ pending

  QueueBranch :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Set
  QueueBranch source visited₁ queue₁ distances₁ =
    IfProp
      (Nonempty (toFSet queue₁))
      (Nonempty (toFSet queue₁) ∧
       ((queue₂ : SetCarrier) →
        (u : Vertex) →
        QueueRemoval
          source visited₁ queue₁ distances₁ queue₂ u))
      (((v₁ : Vertex) →
        member vertexDecEq v₁ (toFSet visited₁) →
        ShortestPath source v₁ (lookup distances₁ v₁)) ∧
       ((v₁ : Vertex) →
        notMember vertexDecEq v₁ (toFSet visited₁) →
        (dv : Int) →
        Not (Path source v₁ dv)))

  MainLoop :
    Vertex →
    Set
  MainLoop source =
    (queue₁ : SetCarrier) →
    (distances₁ : Map Int) →
    (visited₁ : SetCarrier) →
    Inv source visited₁ queue₁ distances₁ ∧
    InvSuccessors source visited₁ queue₁ distances₁ ∧
    MinimumClosure source visited₁ queue₁ distances₁ →
    QueueBranch source visited₁ queue₁ distances₁

  InitialConclusion :
    Vertex →
    SetCarrier →
    SetCarrier →
    Map Int →
    Set
  InitialConclusion source visited queue distances =
    let initialDistances = update distances source zeroZ
    in
    Inv source visited queue initialDistances ∧
    InvSuccessors source visited queue initialDistances ∧
    MinimumClosure source visited queue initialDistances ∧
    MainLoop source

  shortest-path-code'vc : Laws → Set
  shortest-path-code'vc laws =
    (source destination : Vertex) →
    (visited queue : SetCarrier) →
    (distances : Map Int) →
    member vertexDecEq source vertices →
    member vertexDecEq destination vertices →
    setEqual vertexDecEq (toFSet visited) empty →
    setEqual vertexDecEq
      (toFSet queue)
      (insert vertexDecEq source empty) →
    InitialConclusion source visited queue distances
