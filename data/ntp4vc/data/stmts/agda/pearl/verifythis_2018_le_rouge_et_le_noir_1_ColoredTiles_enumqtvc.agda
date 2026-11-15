-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/verifythis_2018_le_rouge_et_le_noir_1_ColoredTiles_enumqtvc: the
-- colored-tile enumeration verification condition, including finite sets of
-- valid colorings, nested loop invariants, and cardinality updates. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module VerifyThis2018LeRougeEtLeNoir1ColoredTilesEnumQtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

zeroZ oneZ twoZ threeZ fourZ fiftyZ fiftyOneZ : Int
zeroZ = pos zero
oneZ = pos 1
twoZ = pos 2
threeZ = pos 3
fourZ = pos 4
fiftyZ = pos 50
fiftyOneZ = pos 51

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthInt : {A : Set} → A → List A → Int → A
nthInt default xs index =
  nthDefault default (toNat index) xs

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value =
  x ∷ setAt xs n value

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

FunctionEq :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEq f g = (x : _) → f x ≡ g x

updateFunction :
  {A : Set} →
  (Int → A) →
  Int →
  A →
  Int →
  A
updateFunction old index value query with intEqual query index
... | true = value
... | false = old query

data Color : Set where
  Red   : Color
  Black : Color

colorEqual : Color → Color → Bool
colorEqual Red Red = true
colorEqual Red Black = false
colorEqual Black Red = false
colorEqual Black Black = true

listEqual :
  {A : Set} →
  (A → A → Bool) →
  List A →
  List A →
  Bool
listEqual equal [] [] = true
listEqual equal [] (_ ∷ _) = false
listEqual equal (_ ∷ _) [] = false
listEqual equal (x ∷ xs) (y ∷ ys) with equal x y
... | true = listEqual equal xs ys
... | false = false

Coloring : Set
Coloring = List Color

coloringEqual : Coloring → Coloring → Bool
coloringEqual = listEqual colorEqual

colorDefault : Color
colorDefault = Black

colorAtNat : Coloring → Nat → Color
colorAtNat coloring index =
  nthDefault colorDefault index coloring

colorAt : Coloring → Int → Color
colorAt coloring index =
  colorAtNat coloring (toNat index)

tworedneighbors : Coloring → Int → Set
tworedneighbors coloring i =
  (colorAt coloring (subtractInt i twoZ) ≡ Red ∧
   colorAt coloring (subtractInt i oneZ) ≡ Red ∧
   twoZ ≤Z i)
  ∨
  (colorAt coloring (subtractInt i oneZ) ≡ Red ∧
   colorAt coloring (addInt i oneZ) ≡ Red ∧
   oneZ ≤Z i ∧
   i ≤Z subtractInt (lengthZ coloring) twoZ)
  ∨
  (colorAt coloring (addInt i oneZ) ≡ Red ∧
   colorAt coloring (addInt i twoZ) ≡ Red ∧
   i ≤Z subtractInt (lengthZ coloring) threeZ)

valid : Coloring → Set
valid coloring =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z lengthZ coloring) →
  colorAt coloring i ≡ Red →
  tworedneighbors coloring i

firstBlackTile : Coloring → Int
firstBlackTile [] = zeroZ
firstBlackTile (Black ∷ rest) = zeroZ
firstBlackTile (Red ∷ rest) =
  addInt oneZ (firstBlackTile rest)

addleft : Int → Coloring → Coloring
addleft (negsuc _) coloring = Black ∷ coloring
addleft (pos zero) coloring = Black ∷ coloring
addleft (pos (suc n)) coloring =
  Red ∷ addleft (pos n) coloring

createFrom :
  {A : Set} →
  Nat →
  Nat →
  (Int → A) →
  List A
createFrom zero index value = []
createFrom (suc count) index value =
  value (natToInt index) ∷
  createFrom count (suc index) value

create : {A : Set} → Int → (Int → A) → List A
create count value =
  createFrom (toNat count) zero value

black : Int → Color
black _ = Black

red : Int → Color
red _ = Red

contains :
  {A : Set} →
  (A → A → Bool) →
  A →
  List A →
  Bool
contains equal sought [] = false
contains equal sought (x ∷ xs) with equal sought x
... | true = true
... | false = contains equal sought xs

nub :
  {A : Set} →
  (A → A → Bool) →
  List A →
  List A
nub equal [] = []
nub equal (x ∷ xs) with contains equal x xs
... | true = nub equal xs
... | false = x ∷ nub equal xs

record FSet (A : Set) : Set where
  constructor fset
  field
    elements : List A

open FSet

empty : {A : Set} → FSet A
empty = fset []

member :
  {A : Set} →
  (A → A → Bool) →
  A →
  FSet A →
  Set
member equal x set =
  contains equal x (elements set) ≡ true

insert :
  {A : Set} →
  (A → A → Bool) →
  A →
  FSet A →
  FSet A
insert equal x set with contains equal x (elements set)
... | true = set
... | false = fset (x ∷ elements set)

unionFrom :
  {A : Set} →
  (A → A → Bool) →
  List A →
  FSet A →
  FSet A
unionFrom equal [] rightSet = rightSet
unionFrom equal (x ∷ xs) rightSet =
  unionFrom equal xs (insert equal x rightSet)

union :
  {A : Set} →
  (A → A → Bool) →
  FSet A →
  FSet A →
  FSet A
union equal leftSet rightSet =
  unionFrom equal (elements leftSet) rightSet

mapSetFrom :
  {A B : Set} →
  (B → B → Bool) →
  (A → B) →
  List A →
  FSet B
mapSetFrom equal target [] = empty
mapSetFrom equal target (x ∷ xs) =
  insert equal (target x) (mapSetFrom equal target xs)

mapSet :
  {A B : Set} →
  (B → B → Bool) →
  (A → B) →
  FSet A →
  FSet B
mapSet equal target set =
  mapSetFrom equal target (elements set)

card : {A : Set} → (A → A → Bool) → FSet A → Nat
card equal set =
  length (nub equal (elements set))

cardZ : {A : Set} → (A → A → Bool) → FSet A → Int
cardZ equal set =
  natToInt (card equal set)

ColoringSet : Set
ColoringSet = FSet Coloring

setDefault : ColoringSet
setDefault = empty

memberColoring : Coloring → ColoringSet → Set
memberColoring = member coloringEqual

singletonColoring : Coloring → ColoringSet
singletonColoring coloring =
  insert coloringEqual coloring empty

unionColoring : ColoringSet → ColoringSet → ColoringSet
unionColoring = union coloringEqual

cardColoring : ColoringSet → Int
cardColoring = cardZ coloringEqual

mapaddleft : ColoringSet → Int → ColoringSet
mapaddleft set count =
  mapSet coloringEqual (addleft count) set

record Array (A : Set) : Set where
  constructor array
  field
    arrayLength   : Nat
    arrayElements : Int → A

open Array

arrayLengthZ : {A : Set} → Array A → Int
arrayLengthZ xs =
  natToInt (arrayLength xs)

updateArray :
  {A : Set} →
  Array A →
  Int →
  A →
  Array A
updateArray xs index value =
  array
    (arrayLength xs)
    (updateFunction (arrayElements xs) index value)

ArraySafe : {A : Set} → Array A → Int → Set
ArraySafe xs index =
  zeroZ ≤Z index ∧ index <Z arrayLengthZ xs

AfterUpdate :
  {A : Set} →
  Array A →
  Int →
  A →
  Set →
  Set
AfterUpdate xs index value continuation =
  arrayLength (updateArray xs index value) ≡ arrayLength xs →
  FunctionEq
    (arrayElements (updateArray xs index value))
    (updateFunction (arrayElements xs) index value) →
  continuation

InitialCount : Array Int → Set
InitialCount count =
  ((i : Int) →
   (zeroZ ≤Z i ∧ i <Z fiftyOneZ) →
   arrayElements count i ≡ zeroZ)
  ∧
  arrayLengthZ count ≡ fiftyOneZ

InitialSets : Array ColoringSet → Set
InitialSets sets =
  ((i : Int) →
   (zeroZ ≤Z i ∧ i <Z fiftyOneZ) →
   arrayElements sets i ≡ empty)
  ∧
  arrayLengthZ sets ≡ fiftyOneZ

BaseInvariant :
  Array ColoringSet →
  Array Int →
  Int →
  Set
BaseInvariant sets count upper =
  ((coloring : Coloring) →
   (zeroZ ≤Z lengthZ coloring ∧ lengthZ coloring <Z upper) →
   valid coloring →
   memberColoring
     coloring
     (arrayElements sets (lengthZ coloring)))
  ∧
  ((coloring : Coloring) →
   (i : Int) →
   (zeroZ ≤Z i ∧ i <Z upper) →
   memberColoring coloring (arrayElements sets i) →
   lengthZ coloring ≡ i ∧ valid coloring)
  ∧
  ((i : Int) →
   (zeroZ ≤Z i ∧ i <Z upper) →
   arrayElements count i ≡
     cardColoring (arrayElements sets i))

AtCurrentLength :
  Array ColoringSet →
  Int →
  Int →
  Set
AtCurrentLength sets n threshold =
  (coloring : Coloring) →
  memberColoring coloring (arrayElements sets n) ↔
    (lengthZ coloring ≡ n ∧
     valid coloring ∧
     firstBlackTile coloring <Z threshold)

InnerInvariant :
  Array ColoringSet →
  Array Int →
  Int →
  Int →
  Set
InnerInvariant sets count n threshold =
  BaseInvariant sets count n ∧
  AtCurrentLength sets n threshold ∧
  arrayElements count n ≡
    cardColoring (arrayElements sets n)

FinalPost :
  Array ColoringSet →
  Array Int →
  Set
FinalPost sets count =
  (arrayLengthZ count ≡ fiftyOneZ ∧
   fiftyOneZ ≡ arrayLengthZ sets)
  ∧
  ((i : Int) →
   (zeroZ ≤Z i ∧ i ≤Z fiftyZ) →
   (coloring : Coloring) →
   lengthZ coloring ≡ i →
   valid coloring ↔
     memberColoring coloring (arrayElements sets i))
  ∧
  ((i : Int) →
   (zeroZ ≤Z i ∧ i <Z fiftyZ) →
   arrayElements count i ≡
     cardColoring (arrayElements sets i))

LastAdd :
  Array ColoringSet →
  Array Int →
  Int →
  Set
LastAdd sets count n =
  zeroZ ≤Z n ∧
  let coloring = create n red
  in
  lengthZ coloring ≡ n ∧
  (((i : Int) →
    (zeroZ ≤Z i ∧ i <Z n) →
    colorAt coloring i ≡ red i) →
   let singleton = singletonColoring coloring
   in
   ArraySafe count n ∧
   let nextCount =
         addInt (arrayElements count n) oneZ
   in
   ArraySafe count n ∧
   AfterUpdate count n nextCount
     (ArraySafe sets n ∧
      let oldSet = arrayElements sets n
          nextSet = unionColoring oldSet singleton
      in
      ((x : Coloring) →
       memberColoring x oldSet →
       Not (memberColoring x singleton))
      ∧
      (cardColoring nextSet ≡
       addInt
         (cardColoring oldSet)
         (cardColoring singleton) →
       ArraySafe sets n ∧
       AfterUpdate sets n nextSet
         (BaseInvariant
           (updateArray sets n nextSet)
           (updateArray count n nextCount)
           (addInt n oneZ)))))

InnerStep :
  Array ColoringSet →
  Array Int →
  Int →
  Int →
  Set
InnerStep sets count n k =
  let earlier = subtractInt (subtractInt n k) oneZ
  in
  ArraySafe count earlier ∧
  ArraySafe count n ∧
  let nextCount =
        addInt
          (arrayElements count n)
          (arrayElements count earlier)
  in
  ArraySafe count n ∧
  AfterUpdate count n nextCount
    (ArraySafe sets earlier ∧
     let newColorings =
           mapaddleft (arrayElements sets earlier) k
     in
     ArraySafe sets n ∧
     let oldSet = arrayElements sets n
         nextSet = unionColoring oldSet newColorings
     in
     ((x : Coloring) →
      memberColoring x oldSet →
      Not (memberColoring x newColorings))
     ∧
     (cardColoring nextSet ≡
      addInt
        (cardColoring oldSet)
        (cardColoring newColorings) →
      ArraySafe sets n ∧
      AfterUpdate sets n nextSet
        (InnerInvariant
          (updateArray sets n nextSet)
          (updateArray count n nextCount)
          n
          (addInt k oneZ))))

InnerLoop :
  Array ColoringSet →
  Array Int →
  Int →
  Int →
  Set
InnerLoop sets count n upper =
  ((sets₂ : Array ColoringSet) →
   (count₂ : Array Int) →
   arrayLength sets₂ ≡ arrayLength sets →
   arrayLength count₂ ≡ arrayLength count →
   (((k : Int) →
     ((threeZ ≤Z k ∧ k ≤Z upper) ∧
      InnerInvariant sets₂ count₂ n k) →
     InnerStep sets₂ count₂ n k)
    ∧
    (InnerInvariant
       sets₂ count₂ n (addInt upper oneZ) →
     LastAdd sets₂ count₂ n)))

OuterStep :
  Array ColoringSet →
  Array Int →
  Int →
  Set
OuterStep sets count n =
  let previous = subtractInt n oneZ
  in
  ArraySafe count previous ∧
  let copiedCount = arrayElements count previous
  in
  ArraySafe count n ∧
  AfterUpdate count n copiedCount
    (ArraySafe sets previous ∧
     let copiedSet =
           mapaddleft
             (arrayElements sets previous)
             zeroZ
     in
     ArraySafe sets n ∧
     AfterUpdate sets n copiedSet
       (let nextCount = updateArray count n copiedCount
            nextSets = updateArray sets n copiedSet
            innerUpper = subtractInt n oneZ
        in
        (threeZ ≤Z addInt innerUpper oneZ →
         BaseInvariant nextSets nextCount n ∧
         AtCurrentLength nextSets n threeZ ∧
         arrayElements nextCount n ≡
           cardColoring (arrayElements nextSets n) ∧
         InnerLoop nextSets nextCount n innerUpper)
        ∧
        (addInt innerUpper oneZ <Z threeZ →
         LastAdd nextSets nextCount n)))

OuterLoops :
  Array ColoringSet →
  Array Int →
  Set
OuterLoops initialSets initialCount =
  (sets : Array ColoringSet) →
  (count : Array Int) →
  arrayLength sets ≡ arrayLength initialSets →
  arrayLength count ≡ arrayLength initialCount →
  (((n : Int) →
    ((fourZ ≤Z n ∧ n ≤Z fiftyZ) ∧
     BaseInvariant sets count n) →
    OuterStep sets count n)
   ∧
   (BaseInvariant
      sets count (addInt fiftyZ oneZ) →
    FinalPost sets count))

AfterInitialUpdates :
  Array ColoringSet →
  Array Int →
  Set
AfterInitialUpdates sets count =
  (fourZ ≤Z addInt fiftyZ oneZ →
   BaseInvariant sets count fourZ ∧
   OuterLoops sets count)
  ∧
  (addInt fiftyZ oneZ <Z fourZ →
   FinalPost sets count)

InitializeSets3 :
  Array ColoringSet →
  Array Int →
  Set
InitializeSets3 sets count =
  let set₃ =
        insert coloringEqual
          (create threeZ red)
          (singletonColoring (create threeZ black))
  in
  ArraySafe sets threeZ ∧
  AfterUpdate sets threeZ set₃
    (AfterInitialUpdates
      (updateArray sets threeZ set₃)
      count)

InitializeCount3 :
  Array ColoringSet →
  Array Int →
  Set
InitializeCount3 sets count =
  ArraySafe count threeZ ∧
  AfterUpdate count threeZ twoZ
    (InitializeSets3
      sets
      (updateArray count threeZ twoZ))

InitializeSets2 :
  Array ColoringSet →
  Array Int →
  Set
InitializeSets2 sets count =
  let set₂ = singletonColoring (create twoZ black)
  in
  ArraySafe sets twoZ ∧
  AfterUpdate sets twoZ set₂
    (InitializeCount3
      (updateArray sets twoZ set₂)
      count)

InitializeCount2 :
  Array ColoringSet →
  Array Int →
  Set
InitializeCount2 sets count =
  ArraySafe count twoZ ∧
  AfterUpdate count twoZ oneZ
    (InitializeSets2
      sets
      (updateArray count twoZ oneZ))

InitializeSets1 :
  Array ColoringSet →
  Array Int →
  Set
InitializeSets1 sets count =
  let set₁ = singletonColoring (create oneZ black)
  in
  ArraySafe sets oneZ ∧
  AfterUpdate sets oneZ set₁
    (InitializeCount2
      (updateArray sets oneZ set₁)
      count)

InitializeCount1 :
  Array ColoringSet →
  Array Int →
  Set
InitializeCount1 sets count =
  ArraySafe count oneZ ∧
  AfterUpdate count oneZ oneZ
    (InitializeSets1
      sets
      (updateArray count oneZ oneZ))

InitializeSets0 :
  Array ColoringSet →
  Array Int →
  Set
InitializeSets0 sets count =
  let set₀ = singletonColoring (create zeroZ black)
  in
  ArraySafe sets zeroZ ∧
  AfterUpdate sets zeroZ set₀
    (InitializeCount1
      (updateArray sets zeroZ set₀)
      count)

InitializeCount0 :
  Array ColoringSet →
  Array Int →
  Set
InitializeCount0 sets count =
  ArraySafe count zeroZ ∧
  AfterUpdate count zeroZ oneZ
    (InitializeSets0
      sets
      (updateArray count zeroZ oneZ))

enum'vc : Set
enum'vc =
  zeroZ ≤Z fiftyOneZ ∧
  ((count : Array Int) →
   InitialCount count →
   zeroZ ≤Z fiftyOneZ ∧
   ((sets : Array ColoringSet) →
    InitialSets sets →
    InitializeCount0 sets count))
