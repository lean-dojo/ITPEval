-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2016_tree_traversal_Iterative_markTreeqtvc: the iterative
-- Morris tree-traversal verification condition, including tree shape,
-- snapshot and call-stack invariants, pointer rotations, termination decrease,
-- and the final marking and restoration conditions. This file contains no proof.

{-# OPTIONS --safe #-}

module TreeTraversalIterativeMarkTreeQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
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

ifValue :
  {P : Set} →
  Dec P →
  {A : Set} →
  A →
  A →
  A
ifValue (yes _) when-true when-false = when-true
ifValue (no _) when-true when-false = when-false

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) = negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

oneN twoN threeN fourN tenN hundredN : Nat
oneN = suc zero
twoN = suc oneN
threeN = suc twoN
fourN = suc threeN
tenN = twoN * (twoN + threeN)
hundredN = tenN * tenN

zeroZ oneZ twoZ threeZ fourZ hundredZ : Int
zeroZ = pos zero
oneZ = pos oneN
twoZ = pos twoN
threeZ = pos threeN
fourZ = pos fourN
hundredZ = pos hundredN

data Kind : Set where
  Parent Left Right : Kind

data Phase : Set where
  GoLeft GoRight GoBack Finish : Phase

data Tree (A : Set) : Set where
  Empty : Tree A
  Node  : Tree A → A → Tree A → Tree A

data Option (A : Set) : Set where
  none : Option A
  some : A → Option A

record TreeTraversalModel : Set₁ where
  field
    Loc             : Set
    Memory          : Set
    defaultMemory   : Memory
    null            : Loc
    accessor        : Memory → Kind → Loc → Loc
    mark            : Memory → Loc → Bool
    excluded-middle : (P : Set) → P ∨ Not P

decide : (model : TreeTraversalModel) → (P : Set) → Dec P
decide model P with TreeTraversalModel.excluded-middle model P
... | left proof = yes proof
... | right refutation = no refutation

module Theory (model : TreeTraversalModel) where

  open TreeTraversalModel model

  Pmem : Set
  Pmem = Kind → Loc → Loc

  Marks : Set
  Marks = Loc → Bool

  TreeLoc : Set
  TreeLoc = Tree Loc

  update :
    {A B : Set} →
    (A → B) →
    A →
    B →
    A →
    B
  update old key value query with decide model (query ≡ key)
  ... | yes _ = value
  ... | no _ = old query

  size : TreeLoc → Int
  size Empty = zeroZ
  size (Node leftTree value rightTree) =
    addInt oneZ (addInt (size leftTree) (size rightTree))

  isTree : Pmem → TreeLoc → Loc → Loc → Set
  isTree pointers Empty cursor parent =
    cursor ≡ null
  isTree pointers (Node leftTree value rightTree) cursor parent =
    Not (cursor ≡ null) ∧
    cursor ≡ value ∧
    pointers Parent cursor ≡ parent ∧
    let leftCursor = pointers Left cursor
        rightCursor = pointers Right cursor
    in
    ((leftCursor ≡ null) ↔ (rightCursor ≡ null)) ∧
    isTree pointers leftTree leftCursor cursor ∧
    isTree pointers rightTree rightCursor cursor

  footprint : TreeLoc → Loc → Set
  footprint Empty location = ⊥
  footprint (Node leftTree value rightTree) location =
    location ≡ value ∨
    (footprint leftTree location ∨ footprint rightTree location)

  ext : (Loc → Set) → Pmem → Pmem → Set
  ext locations pointers1 pointers2 =
    (kind : Kind) →
    (location : Loc) →
    locations location →
    pointers1 kind location ≡ pointers2 kind location

  unchanged : Pmem → Pmem → Set
  unchanged pointers1 pointers2 =
    (kind : Kind) →
    (location : Loc) →
    pointers1 kind location ≡ pointers2 kind location

  wasMarked : TreeLoc → Marks → Marks → Set
  wasMarked tree oldMarks newMarks =
    ((location : Loc) →
      footprint tree location →
      newMarks location ≡ true) ∧
    ((location : Loc) →
      Not (footprint tree location) →
      newMarks location ≡ oldMarks location)

  nextPhase : Phase → Phase
  nextPhase GoLeft = GoRight
  nextPhase GoRight = GoBack
  nextPhase GoBack = GoLeft
  nextPhase Finish = Finish

  rotated : Pmem → Pmem → Phase → Loc → Set
  rotated pointers1 pointers2 phase cursor =
    ((kind : Kind) →
      (location : Loc) →
      Not (location ≡ cursor) →
      pointers1 kind location ≡ pointers2 kind location) ∧
    (Not (phase ≡ Finish) → Not (cursor ≡ null)) ∧
    rotateAtPhase phase
    where
    rotateAtPhase : Phase → Set
    rotateAtPhase GoLeft =
      unchanged pointers1 pointers2
    rotateAtPhase GoRight =
      pointers2 Left cursor ≡ pointers1 Right cursor ∧
      pointers2 Right cursor ≡ pointers1 Parent cursor ∧
      pointers2 Parent cursor ≡ pointers1 Left cursor
    rotateAtPhase GoBack =
      pointers1 Left cursor ≡ pointers2 Right cursor ∧
      pointers1 Right cursor ≡ pointers2 Parent cursor ∧
      pointers1 Parent cursor ≡ pointers2 Left cursor
    rotateAtPhase Finish =
      cursor ≡ null

  record Snap : Set where
    constructor snap
    field
      pointers : Pmem
      cursor   : Loc
      parent   : Loc
      marks    : Marks

  open Snap

  record Frame : Set where
    constructor frame
    field
      memo0  : Snap
      tree   : TreeLoc
      tleft  : TreeLoc
      pleft  : Loc
      tright : TreeLoc
      pright : Loc
      memo1  : Snap
      memo2  : Snap
      memo3  : Snap
      memo4  : Snap

  open Frame

  frameMemo : Frame → Int → Snap
  frameMemo currentFrame pc =
    ifValue (decide model (pc ≤Z zeroZ)) (memo0 currentFrame)
      (ifValue (decide model (pc ≤Z oneZ)) (memo1 currentFrame)
        (ifValue (decide model (pc ≤Z twoZ)) (memo2 currentFrame)
          (ifValue (decide model (pc ≤Z threeZ))
            (memo3 currentFrame)
            (memo4 currentFrame))))

  blocRel : Pmem → Phase → Snap → Snap → Set
  blocRel initialPointers phase state1 state2 =
    parent state2 ≡ cursor state1 ∧
    cursor state2 ≡ pointers state2 Parent (parent state2) ∧
    marks state2 (parent state2) ≡ true ∧
    ((location : Loc) →
      Not (location ≡ parent state2) →
      marks state2 location ≡ marks state1 location) ∧
    IfSet
      (decide model
        ((pointers state1 Left (cursor state1) ≡ null) ∧
         (null ≡ pointers state1 Right (cursor state1))))
      (pointers state2 ≡ pointers state1)
      (rotated
        initialPointers
        (pointers state2)
        (nextPhase phase)
        (parent state2))

  recRel : TreeLoc → Snap → Snap → Set
  recRel currentTree state1 state2 =
    unchanged (pointers state1) (pointers state2) ∧
    cursor state2 ≡ parent state1 ∧
    parent state2 ≡ cursor state1 ∧
    wasMarked currentTree (marks state1) (marks state2)

  data Stack : Set where
    Bottom  : Stack
    Running : Stack → Int → Frame → Stack
    Done    : Stack

  isStack : TreeLoc → Snap → Snap → Stack → Option TreeLoc → Set
  isStack currentTree stop current Bottom calls =
    stop ≡ current ∧ calls ≡ some currentTree
  isStack currentTree stop current (Running rest pc currentFrame) calls =
    (zeroZ ≤Z pc ∧ pc ≤Z fourZ) ∧
    let initial = memo0 currentFrame
    in
    isStack currentTree stop initial rest (some (tree currentFrame)) ∧
    Not (cursor initial ≡ null) ∧
    isTree
      (pointers initial)
      (tree currentFrame)
      (cursor initial)
      (parent initial) ∧
    tree currentFrame ≡
      Node (tleft currentFrame) (cursor initial) (tright currentFrame) ∧
    pleft currentFrame ≡ pointers initial Left (cursor initial) ∧
    pright currentFrame ≡ pointers initial Right (cursor initial) ∧
    (oneZ ≤Z pc →
      blocRel
        (pointers initial)
        GoLeft
        initial
        (memo1 currentFrame) ∧
      Not (pleft currentFrame ≡ null) ∧
      Not (pright currentFrame ≡ null)) ∧
    (twoZ ≤Z pc →
      recRel
        (tleft currentFrame)
        (memo1 currentFrame)
        (memo2 currentFrame)) ∧
    (threeZ ≤Z pc →
      blocRel
        (pointers initial)
        GoRight
        (memo2 currentFrame)
        (memo3 currentFrame)) ∧
    (fourZ ≤Z pc →
      recRel
        (tright currentFrame)
        (memo3 currentFrame)
        (memo4 currentFrame)) ∧
    frameMemo currentFrame pc ≡ current ∧
    callsCondition calls
    where
    callsCondition : Option TreeLoc → Set
    callsCondition none =
      Not (pc ≡ oneZ) ∧ Not (pc ≡ threeZ)
    callsCondition (some calledTree) =
      IfSet
        (decide model (pc ≡ oneZ))
        (calledTree ≡ tleft currentFrame)
        (pc ≡ threeZ ∧ calledTree ≡ tright currentFrame)
  isStack currentTree stop current Done calls =
    recRel currentTree stop current ∧ calls ≡ none

  stackSize : Stack → Int
  stackSize Bottom = oneZ
  stackSize Done = zeroZ
  stackSize (Running rest pc currentFrame) =
    addInt
      (addInt (stackSize rest) (subtractInt hundredZ pc))
      (ifValue
        (decide model (pc ≡ zeroZ))
        (multiplyInt hundredZ
          (addInt (size (tleft currentFrame)) (size (tright currentFrame))))
        (ifValue
          (decide model (pc ≤Z twoZ))
          (multiplyInt hundredZ (size (tright currentFrame)))
          zeroZ))

  phaseAt : Int → Phase
  phaseAt pc with intEqual pc zeroZ
  ... | true = GoLeft
  ... | false with intEqual pc twoZ
  ...   | true = GoRight
  ...   | false = GoBack

  stackBloc : Stack → Snap → Snap → Set
  stackBloc Bottom previous next = ⊥
  stackBloc Done previous next = ⊥
  stackBloc (Running rest pc currentFrame) previous next =
    blocRel
      (pointers (memo0 currentFrame))
      (phaseAt pc)
      previous
      next

  isDone : Stack → Set
  isDone Bottom = ⊥
  isDone (Running rest pc currentFrame) = ⊥
  isDone Done = ⊤

  resultValue : Snap → Bool
  resultValue current =
    ifValue
      (decide model (cursor current ≡ null))
      true
      false

  resultPremise : Bool → Snap → Bool → Set
  resultPremise entered current result =
    result ≡
    ifValue
      (decide model (entered ≡ true))
      (resultValue current)
      false

  resultConclusion : Snap → Bool → Set
  resultConclusion current result =
    (result ≡ true) ↔ (cursor current ≡ null)

  nextStackObligation :
    TreeLoc →
    Snap →
    Snap →
    Stack →
    Loc →
    Loc →
    Pmem →
    Marks →
    Stack →
    Set
  nextStackObligation
    originalTree stop nextState oldStack expectedParent expectedCursor
    expectedPointers expectedMarks nextStack =
    isStack originalTree stop nextState nextStack none ∧
    stackSize nextStack <Z stackSize oldStack →
    (zeroZ ≤Z stackSize oldStack ∧
     stackSize nextStack <Z stackSize oldStack) ∧
    (expectedCursor ≡ null → ⊤) ∧
    pointers nextState ≡ expectedPointers ∧
    cursor nextState ≡ expectedCursor ∧
    parent nextState ≡ expectedParent ∧
    marks nextState ≡ expectedMarks ∧
    isStack originalTree stop nextState nextStack none

  continuationAt :
    TreeLoc →
    Snap →
    Snap →
    Stack →
    Snap →
    Loc →
    Loc →
    Pmem →
    Marks →
    Set
  continuationAt
    originalTree stop previous oldStack nextState expectedParent
    expectedCursor expectedPointers expectedMarks =
    (isStack originalTree stop previous oldStack none ∧
     stackBloc oldStack previous nextState) ∧
    ((nextStack : Stack) →
      nextStackObligation
        originalTree
        stop
        nextState
        oldStack
        expectedParent
        expectedCursor
        expectedPointers
        expectedMarks
        nextStack)

  parentContinuation :
    TreeLoc →
    Snap →
    Snap →
    Stack →
    Memory →
    Set
  parentContinuation originalTree stop current oldStack memory6 =
    Not (cursor current ≡ null) ∧
    ((nextState : Snap) →
      pointers nextState ≡ accessor memory6 ∧
      cursor nextState ≡ accessor memory6 Parent (cursor current) ∧
      parent nextState ≡ cursor current ∧
      marks nextState ≡ mark memory6 →
      continuationAt
        originalTree
        stop
        current
        oldStack
        nextState
        (cursor current)
        (accessor memory6 Parent (cursor current))
        (accessor memory6)
        (mark memory6))

  rotatedContinuation :
    TreeLoc →
    Snap →
    Snap →
    Stack →
    Memory →
    Set
  rotatedContinuation originalTree stop current oldStack memory6 =
    Not (cursor current ≡ null) ∧
    Not (cursor current ≡ null) ∧
    let leftKind = Left
    in
    Not (cursor current ≡ null) ∧
    ((memory7 : Memory) →
      mark memory7 ≡ mark memory6 →
      accessor memory7 ≡
        update
          (accessor memory6)
          leftKind
          (update
            (accessor memory6 leftKind)
            (cursor current)
            (accessor memory6 Right (cursor current))) →
      Not (cursor current ≡ null) ∧
      let rightKind = Right
      in
      Not (cursor current ≡ null) ∧
      ((memory8 : Memory) →
        mark memory8 ≡ mark memory7 →
        accessor memory8 ≡
          update
            (accessor memory7)
            rightKind
            (update
              (accessor memory7 rightKind)
              (cursor current)
              (accessor memory7 Parent (cursor current))) →
        let parentKind = Parent
        in
        Not (cursor current ≡ null) ∧
        ((memory9 : Memory) →
          mark memory9 ≡ mark memory8 →
          accessor memory9 ≡
            update
              (accessor memory8)
              parentKind
              (update
                (accessor memory8 parentKind)
                (cursor current)
                (accessor memory6 Left (cursor current))) →
          ((nextState : Snap) →
            pointers nextState ≡ accessor memory9 ∧
            cursor nextState ≡ accessor memory6 Left (cursor current) ∧
            parent nextState ≡ cursor current ∧
            marks nextState ≡ mark memory9 →
            continuationAt
              originalTree
              stop
              current
              oldStack
              nextState
              (cursor current)
              (accessor memory6 Left (cursor current))
              (accessor memory9)
              (mark memory9)))))

  nonNullContinuation :
    TreeLoc →
    Snap →
    Snap →
    Stack →
    Memory →
    Set
  nonNullContinuation originalTree stop current oldStack memory5 =
    Not (cursor current ≡ null) ∧
    ((memory6 : Memory) →
      accessor memory6 ≡ accessor memory5 →
      mark memory6 ≡
        update (mark memory5) (cursor current) true →
      Not (cursor current ≡ null) ∧
      let leftCursor = accessor memory6 Left (cursor current)
      in
      (leftCursor ≡ null → Not (cursor current ≡ null)) ∧
      ((branchResult : Bool) →
        branchResult ≡
          ifValue
            (decide model (leftCursor ≡ null))
            (ifValue
              (decide model
                (accessor memory6 Right (cursor current) ≡ null))
              true
              false)
            false →
        IfSet
          (decide model (branchResult ≡ true))
          (parentContinuation
            originalTree stop current oldStack memory6)
          (rotatedContinuation
            originalTree stop current oldStack memory6)))

  doneContinuation :
    Memory →
    TreeLoc →
    Loc →
    Snap →
    Stack →
    Memory →
    Set
  doneContinuation initialMemory originalTree root stop oldStack memory5 =
    isDone oldStack ∧
    (isDone oldStack →
      let finalParent = null
          originalPointers = pointers stop
      in
      (ext
        (footprint originalTree)
        originalPointers
        (accessor memory5) ∧
       isTree originalPointers originalTree root finalParent) ∧
      (isTree (accessor memory5) originalTree root finalParent →
        isTree (accessor memory5) originalTree root null ∧
        unchanged
          (accessor initialMemory)
          (accessor memory5) ∧
        wasMarked
          originalTree
          (mark initialMemory)
          (mark memory5)))

  loopBodyVC :
    Memory →
    TreeLoc →
    Loc →
    Snap →
    Bool →
    Stack →
    Snap →
    Memory →
    Set
  loopBodyVC
    initialMemory originalTree root stop entered oldStack current memory5 =
    (cursor current ≡ null → entered ≡ true) ∧
    pointers current ≡ accessor memory5 ∧
    marks current ≡ mark memory5 ∧
    isStack originalTree stop current oldStack none →
    ((result : Bool) →
      resultPremise entered current result →
      resultConclusion current result) ∧
    IfSet
      (decide model (Not (cursor current ≡ null)))
      (nonNullContinuation
        originalTree stop current oldStack memory5)
      (doneContinuation
        initialMemory originalTree root stop oldStack memory5)

  StatementForModel : Set
  StatementForModel =
    (initialMemory : Memory) →
    (originalTree : TreeLoc) →
    (root : Loc) →
    isTree (accessor initialMemory) originalTree root null →
    Not (root ≡ null) →
    let initialParent = null
    in
    (stop : Snap) →
    pointers stop ≡ accessor initialMemory ∧
    cursor stop ≡ root ∧
    parent stop ≡ initialParent ∧
    marks stop ≡ mark initialMemory →
    (isStack originalTree stop stop Bottom (some originalTree) ∧
     isTree (pointers stop) originalTree (cursor stop) (parent stop) ∧
     Not (cursor stop ≡ null)) ∧
    ((currentStack : Stack) →
      isStack originalTree stop stop currentStack none ∧
      stackSize currentStack ≤Z
        addInt
          (stackSize Bottom)
          (multiplyInt hundredZ (size originalTree)) →
      (Not (root ≡ null) ∧
       pointers stop ≡ accessor initialMemory ∧
       cursor stop ≡ root ∧
       parent stop ≡ initialParent ∧
       marks stop ≡ mark initialMemory ∧
       isStack originalTree stop stop currentStack none) ∧
      ((entered : Bool) →
       (oldStack : Stack) →
       (current : Snap) →
       (memory5 : Memory) →
       loopBodyVC
         initialMemory
         originalTree
         root
         stop
         entered
         oldStack
         current
         memory5))

markTree'vc : Set₁
markTree'vc =
  (model : TreeTraversalModel) →
  Theory.StatementForModel model
