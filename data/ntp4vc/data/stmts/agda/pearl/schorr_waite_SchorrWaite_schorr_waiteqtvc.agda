-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/schorr_waite_SchorrWaite_schorr_waiteqtvc: the Schorr-Waite graph
-- traversal verification condition, including its stack and path invariants,
-- pointer-update branches, lexicographic variant, and marking postcondition.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module schorr_waite_SchorrWaite_schorr_waiteqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤Z_ _<Z_ _∈_
infixr 5 _++_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

Not : Set → Set
Not A = A → ⊥

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

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfSet : {P : Set} → Dec P → Set → Set → Set
IfSet (yes _) when-true when-false = when-true
IfSet (no _) when-true when-false = when-false

IfBool : Bool → Set → Set → Set
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

data _∈_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈ (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)

NoDuplicates : {A : Set} → List A → Set
NoDuplicates [] = ⊤
NoDuplicates (x ∷ xs) = Not (x ∈ xs) ∧ NoDuplicates xs

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

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

nthInt : {A : Set} → A → List A → Int → A
nthInt default xs index = nthDefault default (toNat index) xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

_++_ : {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

record SchorrWaiteModel : Set₁ where
  field
    Loc               : Set
    FSet              : Set
    default           : Loc
    null              : Loc
    member            : Loc → FSet → Set
    card              : FSet → Nat
    enumerate         : FSet → List Loc
    insert            : Loc → FSet → FSet
    remove            : Loc → FSet → FSet
    insert-spec       :
      (x y : Loc) (values : FSet) →
      member x (insert y values) ↔ ((x ≡ y) ∨ member x values)
    remove-spec       :
      (x y : Loc) (values : FSet) →
      member x (remove y values) ↔ (member x values ∧ Not (x ≡ y))
    enumerate-spec    :
      (x : Loc) (values : FSet) →
      member x values ↔ x ∈ enumerate values
    enumerate-nodup   :
      (values : FSet) →
      NoDuplicates (enumerate values)
    card-spec         :
      (values : FSet) →
      card values ≡ length (enumerate values)
    extensional       :
      {leftSet rightSet : FSet} →
      ((x : Loc) → member x leftSet ↔ member x rightSet) →
      leftSet ≡ rightSet
    excluded-middle   : (P : Set) → P ∨ Not P

decide : (model : SchorrWaiteModel) → (P : Set) → Dec P
decide model P with SchorrWaiteModel.excluded-middle model P
... | left proof = yes proof
... | right refutation = no refutation

module Theory (model : SchorrWaiteModel) where

  open SchorrWaiteModel model

  update :
    {A : Set} →
    (Loc → A) →
    Loc →
    A →
    Loc →
    A
  update old key value query with decide model (query ≡ key)
  ... | yes _ = value
  ... | no _ = old query

  nthLoc : List Loc → Int → Loc
  nthLoc values index = nthInt default values index

  lastLoc : List Loc → Loc
  lastLoc values = nthLoc values (subtractInt (lengthZ values) oneZ)

  NotInStack : Loc → List Loc → Set
  NotInStack node stack =
    (i : Int) →
    (zeroZ ≤Z i ∧ i <Z lengthZ stack) →
    Not (node ≡ nthLoc stack i)

  Distinct : List Loc → Set
  Distinct stack =
    (i j : Int) →
    (zeroZ ≤Z i ∧ i <Z lengthZ stack) →
    (zeroZ ≤Z j ∧ j <Z lengthZ stack) →
    Not (i ≡ j) →
    Not (nthLoc stack i ≡ nthLoc stack j)

  Edge :
    Loc →
    Loc →
    (Loc → Loc) →
    (Loc → Loc) →
    Set
  Edge x y leftPointer rightPointer =
    Not (x ≡ null) ∧
    ((leftPointer x ≡ y) ∨ (rightPointer x ≡ y))

  data Path
    (leftPointer rightPointer : Loc → Loc) :
    Loc →
    Loc →
    List Loc →
    Set where
    path-nil :
      (x : Loc) →
      Path leftPointer rightPointer x x []
    path-cons :
      {x z y : Loc} {rest : List Loc} →
      Edge x z leftPointer rightPointer →
      Path leftPointer rightPointer z y rest →
      Path leftPointer rightPointer x y (x ∷ rest)

  Reachable :
    (Loc → Loc) →
    (Loc → Loc) →
    Loc →
    Loc →
    Set
  Reachable leftPointer rightPointer x y =
    Σ (List Loc) λ path →
      Path leftPointer rightPointer x y path

  record LoopState : Set where
    constructor loop-state
    field
      cFalseSet     : FSet
      unmarkedSet   : FSet
      path          : List Loc
      stack         : List Loc
      pointer       : Loc
      target        : Loc
      pathFromRoot  : Loc → List Loc
      rightPointer  : Loc → Loc
      leftPointer   : Loc → Loc
      color         : Loc → Bool
      marked        : Loc → Bool

  open LoopState

  cardZ : FSet → Int
  cardZ values = natToInt (card values)

  LexDecrease :
    Int →
    Int →
    Int →
    Int →
    Int →
    Int →
    Set
  LexDecrease newFirst newSecond newThird oldFirst oldSecond oldThird =
    (zeroZ ≤Z oldFirst ∧ newFirst <Z oldFirst) ∨
    ((newFirst ≡ oldFirst) ∧
      ((zeroZ ≤Z oldSecond ∧ newSecond <Z oldSecond) ∨
       ((newSecond ≡ oldSecond) ∧
        (zeroZ ≤Z oldThird ∧ newThird <Z oldThird))))

  VariantDecrease : LoopState → LoopState → Set
  VariantDecrease next current =
    LexDecrease
      (cardZ (unmarkedSet next))
      (cardZ (cFalseSet next))
      (lengthZ (stack next))
      (cardZ (unmarkedSet current))
      (cardZ (cFalseSet current))
      (lengthZ (stack current))

  record Invariant
    (root : Loc)
    (graph : FSet)
    (oldLeft oldRight : Loc → Loc)
    (state : LoopState) :
    Set where
    field
      graph-covered-by-stack :
        (node : Loc) →
        member node graph →
        NotInStack node (stack state) ∨
        Σ Int (λ i → nthLoc (stack state) i ≡ node)

      null-not-in-stack :
        NotInStack null (stack state)

      empty-stack-iff-null-pointer :
        (lengthZ (stack state) ≡ zeroZ) ↔
        (pointer state ≡ null)

      pointer-in-graph :
        Not (pointer state ≡ null) →
        member (pointer state) graph

      stack-head-is-pointer :
        Not (lengthZ (stack state) ≡ zeroZ) →
        nthLoc (stack state) zeroZ ≡ pointer state

      unmarked-tracks-false-mark :
        (node : Loc) →
        member node graph →
        marked state node ≡ false →
        member node (unmarkedSet state)

      cFalse-tracks-false-color :
        (node : Loc) →
        member node graph →
        color state node ≡ false →
        member node (cFalseSet state)

      stack-elements-in-graph :
        (i : Int) →
        (zeroZ ≤Z i ∧ i <Z lengthZ (stack state)) →
        member (nthLoc (stack state) i) graph

      old-edge-orientation-between-stack-elements :
        (i : Int) →
        (zeroZ ≤Z i ∧ i <Z subtractInt (lengthZ (stack state)) oneZ) →
        let nextNode = nthLoc (stack state) i
            previousNode = nthLoc (stack state) (addInt i oneZ)
        in
        IfBool
          (color state previousNode)
          ((oldLeft previousNode ≡ leftPointer state previousNode) ∧
           (oldRight previousNode ≡ nextNode))
          ((oldLeft previousNode ≡ nextNode) ∧
           (oldRight previousNode ≡ rightPointer state previousNode))

      root-path-is-empty :
        pathFromRoot state root ≡ []

      pointers-off-stack-unchanged :
        (node : Loc) →
        member node graph →
        NotInStack node (stack state) →
        (oldLeft node ≡ leftPointer state node) ∧
        (oldRight node ≡ rightPointer state node)

      last-stack-selected-pointer-is-null :
        Not (lengthZ (stack state) ≡ zeroZ) →
        let node = lastLoc (stack state)
        in
        IfBool
          (color state node)
          (rightPointer state node ≡ null)
          (leftPointer state node ≡ null)

      last-stack-element-is-root :
        Not (lengthZ (stack state) ≡ zeroZ) →
        lastLoc (stack state) ≡ root

      selected-current-pointer-links-stack :
        (i : Int) →
        (zeroZ ≤Z i ∧ i <Z subtractInt (lengthZ (stack state)) oneZ) →
        let node = nthLoc (stack state) i
            nextNode = nthLoc (stack state) (addInt i oneZ)
        in
        IfBool
          (color state node)
          (rightPointer state node ≡ nextNode)
          (leftPointer state node ≡ nextNode)

      stack-elements-marked :
        (i : Int) →
        (zeroZ ≤Z i ∧ i <Z lengthZ (stack state)) →
        marked state (nthLoc (stack state) i) ≡ true

      stack-distinct :
        Distinct (stack state)

      unselected-current-pointer-is-old :
        (i : Int) →
        (zeroZ ≤Z i ∧ i <Z lengthZ (stack state)) →
        let node = nthLoc (stack state) i
        in
        IfBool
          (color state node)
          (leftPointer state node ≡ oldLeft node)
          (rightPointer state node ≡ oldRight node)

      pointer-selected-old-child-is-target :
        Not (pointer state ≡ null) →
        IfBool
          (color state (pointer state))
          (oldRight (pointer state) ≡ target state)
          (oldLeft (pointer state) ≡ target state)

      previous-stack-element-is-old-selected-child :
        (i : Int) →
        (zeroZ <Z i ∧ i <Z lengthZ (stack state)) →
        let node = nthLoc (stack state) i
            previousNode = nthLoc (stack state) (subtractInt i oneZ)
        in
        IfBool
          (color state node)
          (oldRight node ≡ previousNode)
          (oldLeft node ≡ previousNode)

      current-pointer-has-root-path :
        Not (pointer state ≡ null) →
        Path oldLeft oldRight root (pointer state) (path state)

      marked-nodes-reachable :
        (node : Loc) →
        member node graph →
        marked state node ≡ true →
        Reachable oldLeft oldRight root node

      null-pointer-target-is-root :
        pointer state ≡ null →
        target state ≡ root

      stored-paths-are-exact :
        (node : Loc) →
        member node graph →
        marked state node ≡ true →
        Path oldLeft oldRight root node (pathFromRoot state node)

      marked-off-stack-children-marked :
        (node : Loc) →
        member node graph →
        Not (node ≡ null) →
        marked state node ≡ true →
        NotInStack node (stack state) →
        ((Not (leftPointer state node ≡ null) →
          marked state (leftPointer state node) ≡ true) ∧
         (Not (rightPointer state node ≡ null) →
          marked state (rightPointer state node) ≡ true))

      color-true-stack-children-marked :
        (i : Int) →
        (zeroZ ≤Z i ∧ i <Z lengthZ (stack state)) →
        color state (nthLoc (stack state) i) ≡ true →
        ((Not (leftPointer state (nthLoc (stack state) i) ≡ null) →
          marked state (leftPointer state (nthLoc (stack state) i)) ≡ true) ∧
         (Not (rightPointer state (nthLoc (stack state) i) ≡ null) →
          marked state (rightPointer state (nthLoc (stack state) i)) ≡ true))

  initialState :
    Loc →
    FSet →
    (Loc → Loc) →
    (Loc → Loc) →
    (Loc → Bool) →
    (Loc → Bool) →
    (Loc → List Loc) →
    LoopState
  initialState root graph leftPointer rightPointer mark colorMap paths =
    loop-state
      graph
      graph
      []
      []
      null
      root
      (update paths root [])
      rightPointer
      leftPointer
      colorMap
      mark

  popState : LoopState → LoopState
  popState state =
    loop-state
      (cFalseSet state)
      (unmarkedSet state)
      (pathFromRoot state (rightPointer state (pointer state)))
      (drop (suc zero) (stack state))
      (rightPointer state (pointer state))
      (pointer state)
      (pathFromRoot state)
      (update
        (rightPointer state)
        (pointer state)
        (target state))
      (leftPointer state)
      (color state)
      (marked state)

  swingState : LoopState → LoopState
  swingState state =
    loop-state
      (remove (pointer state) (cFalseSet state))
      (unmarkedSet state)
      (path state)
      (stack state)
      (pointer state)
      (rightPointer state (pointer state))
      (pathFromRoot state)
      (update
        (rightPointer state)
        (pointer state)
        (leftPointer state (pointer state)))
      (update
        (leftPointer state)
        (pointer state)
        (target state))
      (update (color state) (pointer state) true)
      (marked state)

  pushState : LoopState → List Loc → LoopState
  pushState state newPath =
    loop-state
      (insert (target state) (cFalseSet state))
      (remove (target state) (unmarkedSet state))
      newPath
      (target state ∷ stack state)
      (target state)
      (leftPointer state (target state))
      (update (pathFromRoot state) (target state) newPath)
      (rightPointer state)
      (update
        (leftPointer state)
        (target state)
        (pointer state))
      (update (color state) (target state) false)
      (update (marked state) (target state) true)

  TailFacts : LoopState → Set
  TailFacts state =
    (node : Loc) →
    NotInStack node (stack state) →
    NotInStack node (stack (popState state))

  PushConsFacts : LoopState → Set
  PushConsFacts state =
    (lengthZ (stack (pushState state (path state))) ≡
      addInt oneZ (lengthZ (stack state))) ∧
    ((nthLoc (stack (pushState state (path state))) zeroZ ≡ target state) ∧
     ((i : Int) →
      (zeroZ <Z i ∧ i ≤Z lengthZ (stack state)) →
      nthLoc (stack (pushState state (path state))) i ≡
      nthLoc (stack state) (subtractInt i oneZ)))

  PopBranch :
    (root : Loc) →
    (graph : FSet) →
    (oldLeft oldRight : Loc → Loc) →
    LoopState →
    Set
  PopBranch root graph oldLeft oldRight state =
    (zeroZ <Z lengthZ (stack state)) ∧
    (TailFacts state →
     (Not (pointer state ≡ null) ∧
      (Not (pointer state ≡ null) ∧
       (VariantDecrease (popState state) state ∧
        Invariant root graph oldLeft oldRight (popState state)))))

  SwingBranch :
    (root : Loc) →
    (graph : FSet) →
    (oldLeft oldRight : Loc → Loc) →
    LoopState →
    Set
  SwingBranch root graph oldLeft oldRight state =
    Not (pointer state ≡ null) ∧
    (Not (pointer state ≡ null) ∧
     (Not (pointer state ≡ null) ∧
      (Not (pointer state ≡ null) ∧
       (Not (pointer state ≡ null) ∧
        (VariantDecrease (swingState state) state ∧
         Invariant root graph oldLeft oldRight (swingState state))))))

  PushBranch :
    (root : Loc) →
    (graph : FSet) →
    (oldLeft oldRight : Loc → Loc) →
    LoopState →
    Set
  PushBranch root graph oldLeft oldRight state =
    PushConsFacts state →
    Not (target state ≡ null) ∧
    (Not (target state ≡ null) ∧
     (Not (target state ≡ null) ∧
      IfSet
        (decide model (Not (target state ≡ root)))
        (let newPath = path state ++ (pointer state ∷ [])
         in
         Not (target state ≡ null) ∧
         (Not (target state ≡ null) ∧
          (VariantDecrease (pushState state newPath) state ∧
           Invariant root graph oldLeft oldRight (pushState state newPath))))
        (let newPath = []
         in
         Not (target state ≡ null) ∧
         (Not (target state ≡ null) ∧
          (VariantDecrease (pushState state newPath) state ∧
           Invariant root graph oldLeft oldRight (pushState state newPath))))))

  Postcondition :
    Loc →
    FSet →
    (Loc → Loc) →
    (Loc → Loc) →
    LoopState →
    Set
  Postcondition root graph oldLeft oldRight state =
    ((node : Loc) →
      member node graph →
      (oldLeft node ≡ leftPointer state node) ∧
      (oldRight node ≡ rightPointer state node)) ∧
    (((node : Loc) →
      member node graph →
      marked state node ≡ true →
      Reachable oldLeft oldRight root node) ∧
     ((marked state root ≡ true) ∧
      ((node : Loc) →
       member node graph →
       marked state node ≡ true →
       ((Not (leftPointer state node ≡ null) →
         marked state (leftPointer state node) ≡ true) ∧
        (Not (rightPointer state node ≡ null) →
         marked state (rightPointer state node) ≡ true)))))

  OuterCondition : LoopState → Bool → Set
  OuterCondition state condition =
    (Not (pointer state ≡ null) → condition ≡ true) ∧
    ((pointer state ≡ null) →
      (((Not (target state ≡ null)) →
        ((marked state (target state) ≡ true → condition ≡ false) ∧
         (marked state (target state) ≡ false → condition ≡ true))) ∧
       (target state ≡ null → condition ≡ false)))

  InnerCondition : LoopState → Bool → Set
  InnerCondition state condition =
    (target state ≡ null → condition ≡ true) ∧
    ((Not (target state ≡ null)) →
      ((marked state (target state) ≡ true → condition ≡ true) ∧
       (marked state (target state) ≡ false → condition ≡ false)))

  LoopStepVC :
    Loc →
    FSet →
    (Loc → Loc) →
    (Loc → Loc) →
    LoopState →
    Set
  LoopStepVC root graph oldLeft oldRight state =
    (outer : Bool) →
    OuterCondition state outer →
    IfBool
      outer
      ((inner : Bool) →
       InnerCondition state inner →
       IfBool
         inner
         (Not (pointer state ≡ null) ∧
          IfBool
            (color state (pointer state))
            (PopBranch root graph oldLeft oldRight state)
            (SwingBranch root graph oldLeft oldRight state))
         (PushBranch root graph oldLeft oldRight state))
      (Postcondition root graph oldLeft oldRight state)

  StatementForModel : Set
  StatementForModel =
    (root : Loc) →
    (graph : FSet) →
    (leftPointer rightPointer : Loc → Loc) →
    (mark colorMap : Loc → Bool) →
    (paths : Loc → List Loc) →
    Not (root ≡ null) →
    member root graph →
    ((node : Loc) →
      member node graph →
      (Not (node ≡ null) ∧
       (((leftPointer node ≡ null) ∨ member (leftPointer node) graph) ∧
        ((rightPointer node ≡ null) ∨ member (rightPointer node) graph)))) →
    ((node : Loc) →
      member node graph →
      mark node ≡ false) →
    let start =
          initialState
            root
            graph
            leftPointer
            rightPointer
            mark
            colorMap
            paths
    in
    Invariant root graph leftPointer rightPointer start ∧
    ((state : LoopState) →
      Invariant root graph leftPointer rightPointer state →
      LoopStepVC root graph leftPointer rightPointer state)

schorr-waite'vc : Set₁
schorr-waite'vc =
  (model : SchorrWaiteModel) →
  Theory.StatementForModel model
