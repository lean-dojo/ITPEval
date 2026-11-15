-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc: the
-- recursive Schorr-Waite graph-traversal verification condition for
-- arbitrary-size memory blocks, including body, recursion, loop-invariant,
-- pointer-update, marking, and final reachability obligations.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_ _∈List_
infixr 3 _∧_
infixr 2 _∨_
infix 2 _↔_

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

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
    evidence : P value

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : Not P → Dec P

IfSet : {P : Set} → Dec P → Set → Set → Set
IfSet (yes _) when-true when-false = when-true
IfSet (no _) when-true when-false = when-false

IfBool : Bool → Set → Set → Set
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

data _∈List_ {A : Set} (x : A) : List A → Set where
  here  : {xs : List A} → x ∈List (x ∷ xs)
  there : {y : A} {xs : List A} → x ∈List xs → x ∈List (y ∷ xs)

NoDuplicates : {A : Set} → List A → Set
NoDuplicates [] = ⊤
NoDuplicates (x ∷ xs) = Not (x ∈List xs) ∧ NoDuplicates xs

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

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

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

record SchorrWaiteModel : Set₁ where
  field
    Loc             : Set
    FSet            : Set
    null            : Loc
    empty           : FSet
    insert          : Loc → FSet → FSet
    member          : Loc → FSet → Set
    card            : FSet → Nat
    enumerate       : FSet → List Loc
    insert-spec     :
      (x y : Loc) (values : FSet) →
      member x (insert y values) ↔ ((x ≡ y) ∨ member x values)
    empty-spec      :
      (x : Loc) →
      Not (member x empty)
    enumerate-spec  :
      (x : Loc) (values : FSet) →
      member x values ↔ x ∈List enumerate values
    enumerate-nodup :
      (values : FSet) →
      NoDuplicates (enumerate values)
    card-spec       :
      (values : FSet) →
      card values ≡ length (enumerate values)
    extensional     :
      {leftSet rightSet : FSet} →
      ((x : Loc) → member x leftSet ↔ member x rightSet) →
      leftSet ≡ rightSet
    excluded-middle : (P : Set) → P ∨ Not P

decide : (model : SchorrWaiteModel) → (P : Set) → Dec P
decide model P with SchorrWaiteModel.excluded-middle model P
... | left proof = yes proof
... | right refutation = no refutation

data Color : Set where
  White : Color
  Black : Maybe Int → Color

module Theory (model : SchorrWaiteModel) where

  open SchorrWaiteModel model

  record Memory : Set where
    constructor memory
    field
      block-size : Loc → Int
      accessor   : Loc → Int → Loc
      colors     : Loc → Color

  open Memory

  FunctionEqual :
    {A B : Set} →
    (A → B) →
    (A → B) →
    Set
  FunctionEqual f g = (x : _) → f x ≡ g x

  AccessorEqual :
    (Loc → Int → Loc) →
    (Loc → Int → Loc) →
    Set
  AccessorEqual firstMap secondMap =
    (location : Loc) →
    (index : Int) →
    firstMap location index ≡ secondMap location index

  BlockSizeEqual : Memory → Memory → Set
  BlockSizeEqual firstMemory secondMemory =
    FunctionEqual
      (block-size firstMemory)
      (block-size secondMemory)

  ColorsEqual : Memory → Memory → Set
  ColorsEqual firstMemory secondMemory =
    FunctionEqual
      (colors firstMemory)
      (colors secondMemory)

  MemoryAccessorEqual : Memory → Memory → Set
  MemoryAccessorEqual firstMemory secondMemory =
    AccessorEqual
      (accessor firstMemory)
      (accessor secondMemory)

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

  updateIndex :
    {A : Set} →
    (Int → A) →
    Int →
    A →
    Int →
    A
  updateIndex old key value query with decide model (query ≡ key)
  ... | yes _ = value
  ... | no _ = old query

  updateAccessor :
    (Loc → Int → Loc) →
    Loc →
    Int →
    Loc →
    Loc →
    Int →
    Loc
  updateAccessor old location index value =
    update old location (updateIndex (old location) index value)

  BlackColor : Color → Set
  BlackColor color = color ≠ White

  NotBlack : Color → Set
  NotBlack color = Not (BlackColor color)

  ColorIndexCase : Color → (Int → Set) → Set
  ColorIndexCase White property = ⊥
  ColorIndexCase (Black nothing) property = ⊥
  ColorIndexCase (Black (just index)) property = property index

  ValidIndex : Memory → Loc → Int → Set
  ValidIndex current location index =
    location ≠ null ∧
    zeroZ ≤Z index ∧
    index <Z block-size current location

  ColorIndexValid : Memory → Loc → Set
  ColorIndexValid current location =
    ColorIndexCase
      (colors current location)
      (λ index →
        zeroZ ≤Z index ∧
        index <Z block-size current location)

  Edge : Memory → Loc → Loc → Set
  Edge current from to =
    from ≠ null ∧
    Exists Int
      (λ index →
        (zeroZ ≤Z index ∧
         index <Z block-size current from) ∧
        accessor current from index ≡ to)

  data Path (current : Memory) : Loc → Loc → Set where
    path-nil :
      (location : Loc) →
      Path current location location
    path-cons :
      {from middle to : Loc} →
      Edge current from middle →
      Path current middle to →
      Path current from to

  Subset : FSet → FSet → Set
  Subset firstSet secondSet =
    (location : Loc) →
    member location firstSet →
    member location secondSet

  WellColoredOn :
    FSet →
    FSet →
    Memory →
    (Loc → Color) →
    Set
  WellColoredOn graph gray initial coloring =
    Subset gray graph ∧
    ((x y : Loc) →
      member x graph ∧
      Edge initial x y ∧
      y ≠ null ∧
      BlackColor (coloring x) →
      member x gray ∨ BlackColor (coloring y)) ∧
    ((x : Loc) →
      member x gray →
      BlackColor (coloring x))

  Unchanged : Memory → Memory → Set
  Unchanged old new =
    (location : Loc) →
    (index : Int) →
    ValidIndex old location index →
    accessor new location index ≡ accessor old location index

  StopCondition : Memory → Loc → Loc → Bool → Set
  StopCondition current pointer target answer =
    IfSet
      (decide model (pointer ≡ null))
      (IfSet
        (decide model (target ≡ null))
        (answer ≡ true)
        (IfSet
          (decide model (BlackColor (colors current target)))
          (answer ≡ true)
          (answer ≡ false)))
      (answer ≡ false)

  TargetDoneCondition : Memory → Loc → Bool → Set
  TargetDoneCondition current target answer =
    IfSet
      (decide model (target ≡ null))
      (answer ≡ true)
      (IfSet
        (decide model (BlackColor (colors current target)))
        (answer ≡ true)
        (answer ≡ false))

  BodyPre : Memory → Loc → Loc → Set
  BodyPre current pointer target =
    (pointer ≠ null ∧
     (target ≡ null ∨ BlackColor (colors current target))) →
    ColorIndexValid current pointer

  PopSwingPost :
    Memory →
    Loc →
    Loc →
    Memory →
    Loc →
    Loc →
    Set
  PopSwingPost old pointer target new newPointer newTarget =
    ColorIndexCase
      (colors old pointer)
      (λ oldIndex →
        let nextIndex = addInt oldIndex oneZ
        in
        IfSet
          (decide model
            (nextIndex ≡ block-size old pointer))
          (newTarget ≡ pointer ∧
           newPointer ≡ accessor old pointer oldIndex ∧
           ColorsEqual new old ∧
           AccessorEqual
             (accessor new)
             (updateAccessor
               (accessor old)
               pointer
               oldIndex
               target))
          (newPointer ≡ pointer ∧
           newTarget ≡ accessor old pointer nextIndex ∧
           FunctionEqual
             (colors new)
             (update
               (colors old)
               pointer
               (Black (just nextIndex))) ∧
           AccessorEqual
             (accessor new)
             (updateAccessor
               (updateAccessor
                 (accessor old)
                 pointer
                 nextIndex
                 (accessor old pointer oldIndex))
               pointer
               oldIndex
               target)))

  BodyNormal :
    Memory →
    Loc →
    Loc →
    Memory →
    Loc →
    Loc →
    Set
  BodyNormal old pointer target new newPointer newTarget =
    (pointer ≠ null ∨
     (target ≠ null ∧ NotBlack (colors old target))) ∧
    ((target ≠ null ∧
      NotBlack (colors old target) ∧
      block-size old target ≡ zeroZ) →
      FunctionEqual
        (colors new)
        (update (colors old) target (Black nothing)) ∧
      newTarget ≡ target ∧
      newPointer ≡ pointer ∧
      MemoryAccessorEqual new old) ∧
    ((target ≠ null ∧
      NotBlack (colors old target) ∧
      zeroZ <Z block-size old target) →
      FunctionEqual
        (colors new)
        (update (colors old) target (Black (just zeroZ))) ∧
      newTarget ≡ accessor old target zeroZ ∧
      newPointer ≡ target ∧
      AccessorEqual
        (accessor new)
        (updateAccessor
          (accessor old)
          target
          zeroZ
          pointer)) ∧
    ((target ≡ null ∨ BlackColor (colors old target)) →
      PopSwingPost old pointer target new newPointer newTarget)

  BodyRaises :
    Memory →
    Loc →
    Loc →
    Memory →
    Set
  BodyRaises old pointer target new =
    (pointer ≡ null ∧
     (target ≡ null ∨ BlackColor (colors old target))) ∧
    ColorsEqual new old ∧
    MemoryAccessorEqual new old

  BlackBodyBranch : Memory → Loc → Loc → Set
  BlackBodyBranch old pointer target =
    pointer ≠ null ∧
    ColorIndexCase
      (colors old pointer)
      (λ oldIndex →
        pointer ≠ null ∧
        (zeroZ ≤Z block-size old pointer →
          let nextIndex = addInt oldIndex oneZ
          in
          IfSet
            (decide model
              (nextIndex ≡ block-size old pointer))
            (ValidIndex old pointer oldIndex ∧
             ValidIndex old pointer oldIndex ∧
             ((new : Memory) →
              (BlockSizeEqual new old ∧ ColorsEqual new old) →
              AccessorEqual
                (accessor new)
                (updateAccessor
                  (accessor old)
                  pointer
                  oldIndex
                  target) →
              BodyNormal
                old
                pointer
                target
                new
                (accessor old pointer oldIndex)
                pointer))
            (ValidIndex old pointer nextIndex ∧
             ValidIndex old pointer oldIndex ∧
             ValidIndex old pointer nextIndex ∧
             ((afterFirstWrite : Memory) →
              (BlockSizeEqual afterFirstWrite old ∧
               ColorsEqual afterFirstWrite old) →
              AccessorEqual
                (accessor afterFirstWrite)
                (updateAccessor
                  (accessor old)
                  pointer
                  nextIndex
                  (accessor old pointer oldIndex)) →
              ValidIndex afterFirstWrite pointer oldIndex ∧
              ((afterSecondWrite : Memory) →
               (BlockSizeEqual afterSecondWrite afterFirstWrite ∧
                ColorsEqual afterSecondWrite afterFirstWrite) →
               AccessorEqual
                 (accessor afterSecondWrite)
                 (updateAccessor
                   (accessor afterFirstWrite)
                   pointer
                   oldIndex
                   target) →
               ValidIndex afterSecondWrite pointer nextIndex ∧
               ((new : Memory) →
                (BlockSizeEqual new afterSecondWrite ∧
                 MemoryAccessorEqual new afterSecondWrite) →
                FunctionEqual
                  (colors new)
                  (update
                    (colors afterSecondWrite)
                    pointer
                    (Black (just nextIndex))) →
                BodyNormal
                  old
                  pointer
                  target
                  new
                  pointer
                  (accessor old pointer nextIndex)))))))

  WhiteBodyBranch : Memory → Loc → Loc → Set
  WhiteBodyBranch old pointer target =
    target ≠ null ∧
    (zeroZ ≤Z block-size old target →
      IfSet
        (decide model (block-size old target ≡ zeroZ))
        ((target ≠ null ∧
          block-size old target ≡ zeroZ) ∧
         ((new : Memory) →
          (BlockSizeEqual new old ∧ MemoryAccessorEqual new old) →
          FunctionEqual
            (colors new)
            (update (colors old) target (Black nothing)) →
          BodyNormal old pointer target new pointer target))
        ((ValidIndex old target zeroZ ∧
          ValidIndex old target zeroZ) ∧
         ((afterWrite : Memory) →
          (BlockSizeEqual afterWrite old ∧ ColorsEqual afterWrite old) →
          AccessorEqual
            (accessor afterWrite)
            (updateAccessor
              (accessor old)
              target
              zeroZ
              pointer) →
          ValidIndex afterWrite target zeroZ ∧
          ((new : Memory) →
           (BlockSizeEqual new afterWrite ∧
            MemoryAccessorEqual new afterWrite) →
           FunctionEqual
             (colors new)
             (update
               (colors afterWrite)
               target
               (Black (just zeroZ))) →
           BodyNormal
             old
             pointer
             target
             new
             target
             (accessor old target zeroZ)))))

  BodyImplementationVC : Memory → Set
  BodyImplementationVC initial =
    (pointer target : Loc) →
    (current : Memory) →
    BlockSizeEqual current initial →
    BodyPre current pointer target →
    (stopAnswer : Bool) →
    StopCondition current pointer target stopAnswer →
    IfBool
      stopAnswer
      (pointer ≡ null ∧
       (target ≡ null ∨ BlackColor (colors current target)))
      ((doneAnswer : Bool) →
       TargetDoneCondition current target doneAnswer →
       IfBool
         doneAnswer
         (BlackBodyBranch current pointer target)
         (WhiteBodyBranch current pointer target))

  UnmarkedAccessorsUnchanged :
    Memory →
    Memory →
    Set
  UnmarkedAccessorsUnchanged initial current =
    (location : Loc) →
    (index : Int) →
    (location ≠ null ∧
     NotBlack (colors current location) ∧
     zeroZ ≤Z index ∧
     index <Z block-size current location) →
    accessor current location index ≡
    accessor initial location index

  AuxPre :
    FSet →
    FSet →
    Memory →
    Memory →
    Loc →
    Set
  AuxPre graph gray initial current target =
    WellColoredOn graph gray initial (colors current) ∧
    member target graph ∧
    UnmarkedAccessorsUnchanged initial current

  PreserveColors :
    Memory →
    Memory →
    Memory →
    Loc →
    Set
  PreserveColors initial old new target =
    (location : Loc) →
    location ≠ null →
    (Not (Path initial target location) ∨
     BlackColor (colors old location)) →
    colors new location ≡ colors old location

  AuxStablePost :
    FSet →
    FSet →
    Memory →
    Memory →
    Loc →
    Memory →
    Set
  AuxStablePost graph gray initial old target new =
    Unchanged old new ∧
    WellColoredOn graph gray initial (colors new) ∧
    (BlackColor (colors new target) ∨ target ≡ null) ∧
    PreserveColors initial old new target

  AuxPost :
    FSet →
    FSet →
    Memory →
    Memory →
    Loc →
    Loc →
    Memory →
    Loc →
    Loc →
    Set
  AuxPost graph gray initial old pointer target new newPointer newTarget =
    (newTarget ≡ target ∧ newPointer ≡ pointer) ∧
    Unchanged old new ∧
    WellColoredOn graph gray initial (colors new) ∧
    (BlackColor (colors new newTarget) ∨ newTarget ≡ null) ∧
    PreserveColors initial old new newTarget

  cardZ : FSet → Int
  cardZ values = natToInt (card values)

  VariantDecrease : FSet → FSet → FSet → Set
  VariantDecrease graph gray largerGray =
    zeroZ ≤Z subtractInt (cardZ graph) (cardZ gray) ∧
    subtractInt (cardZ graph) (cardZ largerGray)
      <Z subtractInt (cardZ graph) (cardZ gray)

  LoopInvariant :
    FSet →
    FSet →
    Memory →
    Memory →
    Loc →
    Loc →
    Int →
    Int →
    Memory →
    Loc →
    Loc →
    Set
  LoopInvariant
    graph largerGray initial loopEntry entryPointer entryTarget
    blockSize index current pointer target =
    WellColoredOn graph largerGray initial (colors current) ∧
    pointer ≡ entryTarget ∧
    target ≡ accessor initial pointer index ∧
    colors current pointer ≡ Black (just index) ∧
    ((otherIndex : Int) →
      ((zeroZ ≤Z otherIndex ∧ otherIndex <Z blockSize) ∧
       otherIndex ≠ index) →
      accessor current pointer otherIndex ≡
      accessor loopEntry pointer otherIndex) ∧
    accessor current pointer index ≡ entryPointer ∧
    ((location : Loc) →
      (otherIndex : Int) →
      (location ≠ null ∧
       location ≠ pointer ∧
       zeroZ ≤Z otherIndex ∧
       otherIndex <Z block-size current location) →
      accessor current location otherIndex ≡
      accessor loopEntry location otherIndex) ∧
    ((otherIndex : Int) →
      (zeroZ ≤Z otherIndex ∧ otherIndex <Z index) →
      let location = accessor current pointer otherIndex
      in
      location ≡ null ∨ BlackColor (colors current location)) ∧
    ((location : Loc) →
      location ≠ null →
      (Not (Path initial pointer location) ∨
       BlackColor (colors loopEntry location)) →
      colors current location ≡ colors loopEntry location)

  ExploreThenBody :
    FSet →
    FSet →
    FSet →
    Memory →
    Memory →
    Loc →
    Loc →
    (Memory → Loc → Loc → Set) →
    Set
  ExploreThenBody
    graph gray largerGray initial current pointer target continuation =
    (VariantDecrease graph gray largerGray ∧
     AuxPre graph largerGray initial current target) ∧
    ((afterAux : Memory) →
      BlockSizeEqual afterAux current →
      AuxStablePost
        graph
        largerGray
        initial
        current
        target
        afterAux →
      BodyPre afterAux pointer target ∧
      ((newPointer newTarget : Loc) →
       (afterBody : Memory) →
       BlockSizeEqual afterBody afterAux →
       BodyNormal
         afterAux
         pointer
         target
         afterBody
         newPointer
         newTarget →
       continuation afterBody newPointer newTarget ∧
       Not (BodyRaises afterAux pointer target afterBody)))

  LoopVC :
    FSet →
    FSet →
    FSet →
    Memory →
    Memory →
    Loc →
    Loc →
    Int →
    Memory →
    Loc →
    Loc →
    Set
  LoopVC
    graph gray largerGray initial loopEntry entryPointer entryTarget
    blockSize afterFirstBody firstPointer firstTarget =
    let upper = subtractInt blockSize twoZ
        finalIndex = addInt upper oneZ
    in
    (zeroZ ≤Z finalIndex →
      LoopInvariant
        graph largerGray initial loopEntry entryPointer entryTarget
        blockSize zeroZ afterFirstBody firstPointer firstTarget ∧
      ((pointer target : Loc) →
       (current : Memory) →
       BlockSizeEqual current afterFirstBody →
       (index : Int) →
       ((zeroZ ≤Z index ∧ index ≤Z upper) ∧
        LoopInvariant
          graph largerGray initial loopEntry entryPointer entryTarget
          blockSize index current pointer target) →
       ExploreThenBody
         graph
         gray
         largerGray
         initial
         current
         pointer
         target
         (λ next nextPointer nextTarget →
           LoopInvariant
             graph largerGray initial loopEntry entryPointer entryTarget
             blockSize (addInt index oneZ)
             next nextPointer nextTarget))) ∧
    (((pointer target : Loc) →
      (current : Memory) →
      BlockSizeEqual current afterFirstBody →
      LoopInvariant
        graph largerGray initial loopEntry entryPointer entryTarget
        blockSize finalIndex current pointer target →
      ExploreThenBody
        graph
        gray
        largerGray
        initial
        current
        pointer
        target
        (λ next nextPointer nextTarget →
          AuxPost
            graph gray initial loopEntry entryPointer entryTarget
            next nextPointer nextTarget)) ∧
    (finalIndex <Z zeroZ →
      ExploreThenBody
        graph
        gray
        largerGray
        initial
        afterFirstBody
        firstPointer
        firstTarget
        (λ next nextPointer nextTarget →
          AuxPost
            graph gray initial loopEntry entryPointer entryTarget
            next nextPointer nextTarget)))

  AuxImplementationVC : FSet → Memory → Set
  AuxImplementationVC graph initial =
    (pointer target : Loc) →
    (current : Memory) →
    BlockSizeEqual current initial →
    (gray : FSet) →
    AuxPre graph gray initial current target →
    (doneAnswer : Bool) →
    TargetDoneCondition current target doneAnswer →
    IfBool
      doneAnswer
      (Unchanged current current ∧
       WellColoredOn graph gray initial (colors current) ∧
       (BlackColor (colors current target) ∨ target ≡ null))
      (target ≠ null ∧
       (zeroZ ≤Z block-size current target →
        let blockSize = block-size current target
            largerGray = insert target gray
        in
        BodyPre current pointer target ∧
        ((newPointer newTarget : Loc) →
         (afterFirstBody : Memory) →
         BlockSizeEqual afterFirstBody current →
         BodyNormal
           current
           pointer
           target
           afterFirstBody
           newPointer
           newTarget →
         IfSet
           (decide model (blockSize ≠ zeroZ))
           (LoopVC
             graph gray largerGray initial current pointer target
             blockSize afterFirstBody newPointer newTarget)
           (AuxPost
              graph gray initial current pointer target
              afterFirstBody newPointer newTarget ∧
            Not (BodyRaises
              current pointer target afterFirstBody)))))

  FinalPost : Memory → Loc → Memory → Set
  FinalPost initial root final =
    Unchanged initial final ∧
    ((location : Loc) →
      (Path initial root location ∧ location ≠ null) →
      BlackColor (colors final location)) ∧
    ((location : Loc) →
      (Not (Path initial root location) ∧ location ≠ null) →
      colors final location ≡ colors initial location)

  MainVC : FSet → Memory → Loc → Set
  MainVC graph initial root =
    (WellColoredOn graph empty initial (colors initial) ∧
     member root graph) ∧
    ((afterAux : Memory) →
      BlockSizeEqual afterAux initial →
      AuxStablePost
        graph empty initial initial root afterAux →
      BodyPre afterAux null root ∧
      ((newPointer newTarget : Loc) →
       (afterBody : Memory) →
       BlockSizeEqual afterBody afterAux →
       Not (BodyNormal
         afterAux null root afterBody newPointer newTarget) ∧
       (BodyRaises afterAux null root afterBody →
        FinalPost initial root afterBody)))

  StatementForModel : Set
  StatementForModel =
    (root : Loc) →
    (graph : FSet) →
    (initial : Memory) →
    member root graph →
    ((location : Loc) →
      (index : Int) →
      (member location graph ∧
       location ≠ null ∧
       zeroZ ≤Z index ∧
       index <Z block-size initial location) →
      member (accessor initial location index) graph) →
    ((location : Loc) →
      member location graph →
      NotBlack (colors initial location)) →
    BodyImplementationVC initial ∧
    AuxImplementationVC graph initial ∧
    MainVC graph initial root

schorr-waite'vc : Set₁
schorr-waite'vc =
  (model : SchorrWaiteModel) →
  Theory.StatementForModel model
