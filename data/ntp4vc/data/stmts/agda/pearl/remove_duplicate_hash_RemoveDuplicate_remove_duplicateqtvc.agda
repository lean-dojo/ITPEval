-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/remove_duplicate_hash_RemoveDuplicate_remove_duplicateqtvc: the
-- verification condition for removing duplicate array elements with a mutable
-- finite set, including both loop invariants and cardinal updates.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module remove_duplicate_hash_RemoveDuplicate_remove_duplicateqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤Z_ _<Z_ _≤N_ _∈_
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

_≤N_ : Nat → Nat → Set
x ≤N y = natLessOrEqual x y ≡ true

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

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

nthFunction : {A : Set} → A → List A → Int → A
nthFunction default xs index = nthInt default xs index

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

IfSet : {P : Set} → Dec P → Set → Set → Set
IfSet (yes _) when-true when-false = when-true
IfSet (no _) when-true when-false = when-false

record MutableSetModel : Set₁ where
  field
    E                 : Set
    S                 : Set
    FSet              : Set
    default           : E
    defaultState      : S
    empty             : FSet
    insert            : E → FSet → FSet
    member            : E → FSet → Set
    card              : FSet → Nat
    enumerate         : FSet → List E
    empty-spec        : (x : E) → Not (member x empty)
    insert-spec       :
      (x y : E) (values : FSet) →
      member x (insert y values) ↔ ((x ≡ y) ∨ member x values)
    enumerate-spec    :
      (x : E) (values : FSet) →
      member x values ↔ x ∈ enumerate values
    enumerate-nodup   :
      (values : FSet) →
      NoDuplicates (enumerate values)
    card-spec         :
      (values : FSet) →
      card values ≡ length (enumerate values)
    extensional       :
      {leftSet rightSet : FSet} →
      ((x : E) → member x leftSet ↔ member x rightSet) →
      leftSet ≡ rightSet
    toFSet            : S → FSet
    choose            : S → E
    choose-spec       :
      (state : S) →
      Not (toFSet state ≡ empty) →
      member (choose state) (toFSet state)
    excluded-middle   : (P : Set) → P ∨ Not P

open MutableSetModel

decide : (model : MutableSetModel) → (P : Set) → Dec P
decide model P with excluded-middle model P
... | left proof = yes proof
... | right refutation = no refutation

Subset :
  (model : MutableSetModel) →
  FSet model →
  FSet model →
  Set
Subset model firstSet secondSet =
  (x : E model) →
  member model x firstSet →
  member model x secondSet

Appears :
  (model : MutableSetModel) →
  E model →
  List (E model) →
  Int →
  Set
Appears model value array upper =
  Σ Int λ i →
    ((zeroZ ≤Z i) ∧ (i <Z upper)) ∧
    (nthInt (default model) array i ≡ value)

NoDupPrefix :
  (model : MutableSetModel) →
  List (E model) →
  Int →
  Set
NoDupPrefix model array upper =
  (i : Int) →
  ((zeroZ ≤Z i) ∧ (i <Z upper)) →
  Not
    (Appears
      model
      (nthInt (default model) array i)
      array
      i)

AppearsSet :
  (model : MutableSetModel) →
  List (E model) →
  Int →
  S model →
  Set
AppearsSet model array upper state =
  (x : E model) →
  Appears model x array upper ↔
  member model x (toFSet model state)

SetAppears :
  (model : MutableSetModel) →
  S model →
  List (E model) →
  Int →
  Set
SetAppears model state array upper =
  (x : E model) →
  member model x (toFSet model state) ↔
  Appears model x array upper

IndexBounds :
  (model : MutableSetModel) →
  List (E model) →
  Int →
  Set
IndexBounds model array i =
  (zeroZ ≤Z i) ∧ (i <Z lengthZ array)

CounterInvariant :
  (model : MutableSetModel) →
  List (E model) →
  Int →
  S model →
  Set
CounterInvariant model array j state =
  (zeroZ ≤Z j) ∧
  (j ≡ natToInt (card model (toFSet model state))) ∧
  (card model (toFSet model state) ≤N length array)

SecondInvariant :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  List (E model) →
  Int →
  S model →
  Int →
  Set
SecondInvariant model input saved output j state i =
  AppearsSet model input i state ∧
  SetAppears model state output j ∧
  NoDupPrefix model output j ∧
  CounterInvariant model output j state ∧
  Subset model (toFSet model state) (toFSet model saved)

Postcondition :
  (model : MutableSetModel) →
  List (E model) →
  List (E model) →
  Set
Postcondition model input output =
  NoDupPrefix model output (lengthZ output) ∧
  ((x : E model) →
    Appears model x input (lengthZ input) ↔
    Appears model x output (lengthZ output))

AddSpec :
  (model : MutableSetModel) →
  S model →
  E model →
  S model →
  Set
AddSpec model oldState value newState =
  (toFSet model newState ≡
    insert model value (toFSet model oldState)) ∧
  IfSet
    (decide model (member model value (toFSet model oldState)))
    (card model (toFSet model newState) ≡
      card model (toFSet model oldState))
    (natToInt (card model (toFSet model newState)) ≡
      addInt
        (natToInt (card model (toFSet model oldState)))
        oneZ)

FirstAddTransition :
  (model : MutableSetModel) →
  List (E model) →
  Int →
  S model →
  Set
FirstAddTransition model input i oldState =
  let value = nthInt (default model) input i
  in
  (newState : S model) →
  AddSpec model oldState value newState →
  AppearsSet model input (addInt i oneZ) newState

InitialOutput :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  List (E model) →
  Set
InitialOutput model input saved output =
  (i : Int) →
  ((zeroZ ≤Z i) ∧
    (i <Z natToInt (card model (toFSet model saved)))) →
  nthInt (default model) output i ≡
  nthInt (default model) input zeroZ

UpdatedOutputConclusion :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  Int →
  List (E model) →
  Int →
  S model →
  S model →
  Set
UpdatedOutputConclusion
  model input saved i output j oldState newState =
  let value = nthInt (default model) input i
      updated = setAt output (toNat j) value
  in
  IndexBounds model input i ∧
  ((zeroZ ≤Z j) ∧ (j <Z lengthZ output)) ∧
  ((length updated ≡ length output) →
    (nthFunction (default model) updated ≡
      updateFunction
        (nthFunction (default model) output)
        j
        value) →
    SecondInvariant
      model
      input
      saved
      updated
      (addInt j oneZ)
      newState
      (addInt i oneZ))

NonMemberBranch :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  Int →
  List (E model) →
  Int →
  S model →
  Set
NonMemberBranch model input saved i output j oldState =
  IndexBounds model input i ∧
  (let value = nthInt (default model) input i
   in
   (newState : S model) →
   AddSpec model oldState value newState →
   UpdatedOutputConclusion
     model input saved i output j oldState newState)

SecondStep :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  Int →
  List (E model) →
  Int →
  S model →
  Set
SecondStep model input saved i output j state =
  let value = nthInt (default model) input i
  in
  IndexBounds model input i ∧
  IfSet
    (decide model (Not (member model value (toFSet model state))))
    (NonMemberBranch model input saved i output j state)
    (SecondInvariant
      model
      input
      saved
      output
      j
      state
      (addInt i oneZ))

SecondLoopObligation :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  List (E model) →
  Int →
  Set
SecondLoopObligation model input saved initialOutput lastIndex =
  (j : Int) →
  (output : List (E model)) →
  (state : S model) →
  (length output ≡ length initialOutput) →
  (((i : Int) →
    (((zeroZ ≤Z i) ∧ (i ≤Z lastIndex)) ∧
      SecondInvariant model input saved output j state i) →
    SecondStep model input saved i output j state) ∧
   (SecondInvariant
      model
      input
      saved
      output
      j
      state
      (addInt lastIndex oneZ) →
    Postcondition model input output))

InitialSecondInvariant :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  List (E model) →
  S model →
  Set
InitialSecondInvariant model input saved output state =
  AppearsSet model input zeroZ state ∧
  SetAppears model state output zeroZ ∧
  NoDupPrefix model output zeroZ ∧
  CounterInvariant model output zeroZ state ∧
  Subset model (toFSet model state) (toFSet model saved)

SecondLoopVC :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  List (E model) →
  S model →
  Set
SecondLoopVC model input saved output state =
  let lastIndex = subtractInt (lengthZ input) oneZ
      duration = addInt lastIndex oneZ
  in
  ((zeroZ ≤Z duration) →
    InitialSecondInvariant model input saved output state ∧
    SecondLoopObligation model input saved output lastIndex) ∧
  ((duration <Z zeroZ) →
    Postcondition model input output)

AllocateAndRunSecondLoop :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  Set
AllocateAndRunSecondLoop model input saved =
  let outputLength = natToInt (card model (toFSet model saved))
  in
  (zeroZ ≤Z outputLength) ∧
  ((output : List (E model)) →
    (InitialOutput model input saved output ∧
      (lengthZ output ≡ outputLength)) →
    ((state : S model) →
      (toFSet model state ≡ empty model) →
      SecondLoopVC model input saved output state))

FirstLoopObligation :
  (model : MutableSetModel) →
  List (E model) →
  Int →
  Set
FirstLoopObligation model input lastIndex =
  (state : S model) →
  (((i : Int) →
    (((zeroZ ≤Z i) ∧ (i ≤Z lastIndex)) ∧
      AppearsSet model input i state) →
    (IndexBounds model input i ∧
      FirstAddTransition model input i state)) ∧
   (AppearsSet model input (addInt lastIndex oneZ) state →
    (IndexBounds model input zeroZ ∧
      AllocateAndRunSecondLoop model input state)))

RemoveDuplicateBody :
  (model : MutableSetModel) →
  List (E model) →
  S model →
  Set
RemoveDuplicateBody model input initialState =
  let lastIndex = subtractInt (lengthZ input) oneZ
      duration = addInt lastIndex oneZ
  in
  ((zeroZ ≤Z duration) →
    AppearsSet model input zeroZ initialState ∧
    FirstLoopObligation model input lastIndex) ∧
  ((duration <Z zeroZ) →
    IndexBounds model input zeroZ ∧
    AllocateAndRunSecondLoop model input initialState)

remove-duplicate'vc : Set₁
remove-duplicate'vc =
  (model : MutableSetModel) →
  (input : List (E model)) →
  (initialState : S model) →
  (oneZ ≤Z lengthZ input) →
  (toFSet model initialState ≡ empty model) →
  (natToInt (card model (toFSet model initialState)) ≡ zeroZ) →
  RemoveDuplicateBody model input initialState
