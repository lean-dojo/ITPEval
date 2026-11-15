-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2016_tree_traversal_Recursive_markTreeqtvc: the recursive
-- Morris tree-traversal verification condition, including pointer rotations,
-- recursive subtree traversal, marking, and restoration of tree shape.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module TreeTraversalRecursiveMarkTreeQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

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

data Kind : Set where
  Parent Left Right : Kind

data Phase : Set where
  GoLeft GoRight GoBack Finish : Phase

data Tree (A : Set) : Set where
  Empty : Tree A
  Node  : Tree A → A → Tree A → Tree A

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

  sameMarks : Marks → Marks → Set
  sameMarks marks1 marks2 =
    (location : Loc) →
    marks1 location ≡ marks2 location

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

  nonEmptyTree : TreeLoc → Set
  nonEmptyTree Empty = ⊥
  nonEmptyTree (Node leftTree value rightTree) = ⊤

  hasChildren : TreeLoc → TreeLoc → TreeLoc → Set
  hasChildren Empty leftTree rightTree = ⊥
  hasChildren (Node actualLeft value actualRight) leftTree rightTree =
    leftTree ≡ actualLeft ∧ rightTree ≡ actualRight

  isImmediateSubtree : TreeLoc → TreeLoc → Set
  isImmediateSubtree Empty subtree = ⊥
  isImmediateSubtree (Node leftTree value rightTree) subtree =
    leftTree ≡ subtree ∨ rightTree ≡ subtree

  leafBlocResult :
    Pmem →
    Memory →
    Phase →
    Loc →
    Memory →
    Set
  leafBlocResult initialPointers memory1 phase cursor memory2 =
    Not (cursor ≡ null) ∧
    Not (phase ≡ Finish) ∧
    mark memory2 cursor ≡ true ∧
    ((location : Loc) →
      Not (location ≡ cursor) →
      mark memory2 location ≡ mark memory1 location) ∧
    IfSet
      (decide model
        ((accessor memory1 Left cursor ≡ null) ∧
         (null ≡ accessor memory1 Right cursor)))
      (unchanged (accessor memory2) (accessor memory1))
      (rotated
        initialPointers
        (accessor memory2)
        (nextPhase phase)
        cursor)

  rotatedBlocResult :
    Pmem →
    Memory →
    Phase →
    Loc →
    Memory →
    Set
  rotatedBlocResult initialPointers memory1 phase cursor memory2 =
    Not (cursor ≡ null) ∧
    Not (cursor ≡ null) ∧
    let leftKind = Left
    in
    Not (cursor ≡ null) ∧
    ((memory3 : Memory) →
      sameMarks (mark memory3) (mark memory2) →
      unchanged
        (accessor memory3)
        (update
          (accessor memory2)
          leftKind
          (update
            (accessor memory2 leftKind)
            cursor
            (accessor memory2 Right cursor))) →
      Not (cursor ≡ null) ∧
      let rightKind = Right
      in
      Not (cursor ≡ null) ∧
      ((memory4 : Memory) →
        sameMarks (mark memory4) (mark memory3) →
        unchanged
          (accessor memory4)
          (update
            (accessor memory3)
            rightKind
            (update
              (accessor memory3 rightKind)
              cursor
              (accessor memory3 Parent cursor))) →
        let parentKind = Parent
        in
        Not (cursor ≡ null) ∧
        ((memory5 : Memory) →
          sameMarks (mark memory5) (mark memory4) →
          unchanged
            (accessor memory5)
            (update
              (accessor memory4)
              parentKind
              (update
                (accessor memory4 parentKind)
                cursor
                (accessor memory2 Left cursor))) →
          accessor memory2 Left cursor ≡
            accessor memory5 Parent cursor ∧
          Not (phase ≡ Finish) ∧
          mark memory5 cursor ≡ true ∧
          ((location : Loc) →
            Not (location ≡ cursor) →
            mark memory5 location ≡ mark memory1 location) ∧
          IfSet
            (decide model
              ((accessor memory1 Left cursor ≡ null) ∧
               (null ≡ accessor memory1 Right cursor)))
            (unchanged (accessor memory5) (accessor memory1))
            (rotated
              initialPointers
              (accessor memory5)
              (nextPhase phase)
              cursor))))

  afterMarkBlocVC :
    Pmem →
    Memory →
    Phase →
    Loc →
    Memory →
    Set
  afterMarkBlocVC initialPointers memory1 phase cursor memory2 =
    Not (cursor ≡ null) ∧
    let leftCursor = accessor memory2 Left cursor
    in
    (leftCursor ≡ null → Not (cursor ≡ null)) ∧
    ((branchResult : Bool) →
      IfSet
        (decide model (leftCursor ≡ null))
        (branchResult ≡
          ifValue
            (decide model
              (accessor memory2 Right cursor ≡ null))
            true
            false)
        (branchResult ≡ false) →
      IfSet
        (decide model (branchResult ≡ true))
        (leafBlocResult
          initialPointers memory1 phase cursor memory2)
        (rotatedBlocResult
          initialPointers memory1 phase cursor memory2))

  blocVC :
    Bool →
    Loc →
    Memory →
    Pmem →
    Phase →
    Set
  blocVC entered cursor memory1 initialPointers phase =
    rotated initialPointers (accessor memory1) phase cursor ∧
    (phase ≡ Finish → entered ≡ true) →
    ((stopResult : Bool) →
      IfSet
        (decide model (entered ≡ true))
        (stopResult ≡
          ifValue
            (decide model (cursor ≡ null))
            true
            false)
        (stopResult ≡ false) →
      IfSet
        (decide model (stopResult ≡ true))
        (phase ≡ Finish)
        (Not (cursor ≡ null) ∧
         ((memory2 : Memory) →
          unchanged (accessor memory2) (accessor memory1) →
          sameMarks
            (mark memory2)
            (update (mark memory1) cursor true) →
          afterMarkBlocVC
            initialPointers memory1 phase cursor memory2)))

  resultVC :
    Loc →
    Loc →
    TreeLoc →
    TreeLoc →
    Bool →
    Set
  resultVC leftCursor rightCursor leftTree rightTree result =
    IfSet
      (decide model (leftCursor ≡ null))
      (result ≡
        ifValue
          (decide model (rightCursor ≡ null))
          true
          false)
      (result ≡ false) →
    ((result ≡ true) ↔
      ((leftCursor ≡ null) ∧ (rightCursor ≡ null))) ∧
    (result ≡ true →
      leftTree ≡ Empty ∧ rightTree ≡ Empty)

  afterGoBack :
    TreeLoc →
    Loc →
    Loc →
    Memory →
    Pmem →
    Memory →
    Set
  afterGoBack currentTree parent cursor memory1 initialPointers memory5 =
    let goBackPhase = GoBack
    in
    rotated
      initialPointers
      (accessor memory5)
      goBackPhase
      cursor ∧
    ((memory6 : Memory) →
      mark memory6 cursor ≡ true ∧
      ((location : Loc) →
        Not (location ≡ cursor) →
        mark memory6 location ≡ mark memory5 location) ∧
      IfSet
        (decide model
          ((accessor memory5 Left cursor ≡ null) ∧
           (null ≡ accessor memory5 Right cursor)))
        (unchanged (accessor memory6) (accessor memory5))
        (rotated
          initialPointers
          (accessor memory6)
          (nextPhase goBackPhase)
          cursor) →
      unchanged (accessor memory1) (accessor memory6) ∧
      accessor memory6 Parent cursor ≡ parent ∧
      wasMarked currentTree (mark memory1) (mark memory6))

  afterRightTraversal :
    TreeLoc →
    TreeLoc →
    Loc →
    Loc →
    Loc →
    Loc →
    Memory →
    Pmem →
    Memory →
    Set
  afterRightTraversal
    currentTree rightTree leftCursor rightCursor parent cursor
    memory1 initialPointers memory4 =
    (ext
      (footprint rightTree)
      initialPointers
      (accessor memory4) ∧
     isTree initialPointers rightTree rightCursor cursor) ∧
    (isTree (accessor memory4) rightTree rightCursor cursor →
      (isImmediateSubtree currentTree rightTree ∧
       Not (accessor memory4 Parent cursor ≡ null) ∧
       isTree
         (accessor memory4)
         rightTree
         (accessor memory4 Parent cursor)
         cursor) ∧
      ((memory5 : Memory) →
        unchanged (accessor memory4) (accessor memory5) ∧
        wasMarked
          rightTree
          (mark memory4)
          (mark memory5) →
        afterGoBack
          currentTree
          parent
          cursor
          memory1
          initialPointers
          memory5))

  afterLeftTraversal :
    TreeLoc →
    TreeLoc →
    TreeLoc →
    Loc →
    Loc →
    Loc →
    Loc →
    Memory →
    Pmem →
    Memory →
    Set
  afterLeftTraversal
    currentTree leftTree rightTree leftCursor rightCursor parent cursor
    memory1 initialPointers memory2 =
    (ext
      (footprint leftTree)
      initialPointers
      (accessor memory2) ∧
     isTree initialPointers leftTree leftCursor cursor) ∧
    (isTree (accessor memory2) leftTree leftCursor cursor →
      (isImmediateSubtree currentTree leftTree ∧
       Not (accessor memory2 Parent cursor ≡ null) ∧
       isTree
         (accessor memory2)
         leftTree
         (accessor memory2 Parent cursor)
         cursor) ∧
      ((memory3 : Memory) →
        unchanged (accessor memory2) (accessor memory3) ∧
        wasMarked
          leftTree
          (mark memory2)
          (mark memory3) →
        let goRightPhase = GoRight
        in
        rotated
          initialPointers
          (accessor memory3)
          goRightPhase
          cursor ∧
        ((memory4 : Memory) →
          mark memory4 cursor ≡ true ∧
          ((location : Loc) →
            Not (location ≡ cursor) →
            mark memory4 location ≡ mark memory3 location) ∧
          IfSet
            (decide model
              ((accessor memory3 Left cursor ≡ null) ∧
               (null ≡ accessor memory3 Right cursor)))
            (unchanged (accessor memory4) (accessor memory3))
            (rotated
              initialPointers
              (accessor memory4)
              (nextPhase goRightPhase)
              cursor) →
          afterRightTraversal
            currentTree
            rightTree
            leftCursor
            rightCursor
            parent
            cursor
            memory1
            initialPointers
            memory4)))

  subtreeBranchVC :
    TreeLoc →
    TreeLoc →
    TreeLoc →
    Loc →
    Loc →
    Loc →
    Loc →
    Memory →
    Pmem →
    Memory →
    Set
  subtreeBranchVC
    currentTree leftTree rightTree leftCursor rightCursor parent cursor
    memory1 initialPointers memory2 =
    ((result : Bool) →
      resultVC leftCursor rightCursor leftTree rightTree result) ∧
    ((leftCursor ≡ null ∧ rightCursor ≡ null →
      leftTree ≡ Empty ∧ rightTree ≡ Empty) →
      IfSet
        (decide model
          (Not ((leftCursor ≡ null) ∧ (rightCursor ≡ null))))
        (afterLeftTraversal
          currentTree
          leftTree
          rightTree
          leftCursor
          rightCursor
          parent
          cursor
          memory1
          initialPointers
          memory2)
        (unchanged (accessor memory1) (accessor memory2) ∧
         accessor memory2 Parent cursor ≡ parent ∧
         wasMarked currentTree (mark memory1) (mark memory2)))

  afterFirstBloc :
    TreeLoc →
    TreeLoc →
    TreeLoc →
    Loc →
    Loc →
    Loc →
    Loc →
    Memory →
    Pmem →
    Memory →
    Set
  afterFirstBloc
    currentTree leftTree rightTree leftCursor rightCursor parent cursor
    memory1 initialPointers memory2 =
    mark memory2 cursor ≡ true ∧
    ((location : Loc) →
      Not (location ≡ cursor) →
      mark memory2 location ≡ mark memory1 location) ∧
    IfSet
      (decide model
        ((accessor memory1 Left cursor ≡ null) ∧
         (null ≡ accessor memory1 Right cursor)))
      (unchanged (accessor memory2) (accessor memory1))
      (rotated
        initialPointers
        (accessor memory2)
        (nextPhase GoLeft)
        cursor) →
    subtreeBranchVC
      currentTree
      leftTree
      rightTree
      leftCursor
      rightCursor
      parent
      cursor
      memory1
      initialPointers
      memory2

  recursiveCaseVC :
    Loc →
    Loc →
    Memory →
    TreeLoc →
    Set
  recursiveCaseVC parent cursor memory1 currentTree =
    Not (cursor ≡ null) ∧
    isTree (accessor memory1) currentTree cursor parent →
    let initialPointers = accessor memory1
    in
    Not (cursor ≡ null) ∧
    let leftCursor = accessor memory1 Left cursor
    in
    Not (cursor ≡ null) ∧
    let rightCursor = accessor memory1 Right cursor
    in
    nonEmptyTree currentTree ∧
    ((leftTree rightTree : TreeLoc) →
      hasChildren currentTree leftTree rightTree →
      isTree
        initialPointers
        (Node leftTree cursor rightTree)
        cursor
        parent ∧
      (Not (footprint leftTree cursor) ∧
       Not (footprint rightTree cursor) →
       rotated
         initialPointers
         (accessor memory1)
         GoLeft
         cursor ∧
       ((memory2 : Memory) →
         afterFirstBloc
           currentTree
           leftTree
           rightTree
           leftCursor
           rightCursor
           parent
           cursor
           memory1
           initialPointers
           memory2)))

  finalVC :
    Memory →
    TreeLoc →
    Loc →
    Loc →
    Set
  finalVC initialMemory originalTree root initialParent =
    let initialPointers = accessor initialMemory
    in
    (Not (root ≡ null) ∧
     isTree (accessor initialMemory) originalTree root initialParent) ∧
    ((memory1 : Memory) →
      unchanged
        (accessor initialMemory)
        (accessor memory1) ∧
      wasMarked
        originalTree
        (mark initialMemory)
        (mark memory1) →
      rotated
        initialPointers
        (accessor memory1)
        Finish
        initialParent ∧
      ((cursor : Loc) →
        rotated
          initialPointers
          (accessor memory1)
          Finish
          cursor →
        rotated
          initialPointers
          (accessor memory1)
          Finish
          cursor ∧
        let finalParent = null
        in
        (ext
          (footprint originalTree)
          initialPointers
          (accessor memory1) ∧
         isTree
           initialPointers
           originalTree
           root
           finalParent) ∧
        (isTree
          (accessor memory1)
          originalTree
          root
          finalParent →
          isTree
            (accessor memory1)
            originalTree
            root
            null ∧
          unchanged
            (accessor initialMemory)
            (accessor memory1) ∧
          wasMarked
            originalTree
            (mark initialMemory)
            (mark memory1))))

  StatementForModel : Set
  StatementForModel =
    (initialMemory : Memory) →
    (originalTree : TreeLoc) →
    (root : Loc) →
    isTree
      (accessor initialMemory)
      originalTree
      root
      null →
    Not (root ≡ null) →
    let initialParent = null
    in
    ((entered : Bool) →
      (cursor : Loc) →
      (memory1 : Memory) →
      (initialPointers : Pmem) →
      (phase : Phase) →
      blocVC entered cursor memory1 initialPointers phase) ∧
    (((parent cursor : Loc) →
      (memory1 : Memory) →
      (currentTree : TreeLoc) →
      recursiveCaseVC parent cursor memory1 currentTree) ∧
     finalVC initialMemory originalTree root initialParent)

markTree'vc : Set₁
markTree'vc =
  (model : TreeTraversalModel) →
  Theory.StatementForModel model
