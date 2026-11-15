-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linear_probing_LinearProbing_removeqtvc: the verification condition
-- for removing a key from a linear-probing hash table, including probing,
-- array clearing, counting, validity, and view-update obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module linear_probing_LinearProbing_removeqtvc where

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

IfNat : Bool → Nat → Nat → Nat
IfNat true when-true when-false = when-true
IfNat false when-true when-false = when-false

natModFuel : Nat → Nat → Nat → Nat
natModFuel zero dividend divisor = dividend
natModFuel (suc fuel) dividend zero = dividend
natModFuel (suc fuel) dividend (suc divisor) =
  IfNat
    (natLess dividend (suc divisor))
    dividend
    (natModFuel
      fuel
      (natSubtract dividend (suc divisor))
      (suc divisor))

natMod : Nat → Nat → Nat
natMod dividend divisor =
  natModFuel (suc dividend) dividend divisor

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

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

tmodInt : Int → Int → Int
tmodInt (pos n) divisor =
  pos (natMod n (absoluteNat divisor))
tmodInt (negsuc n) divisor =
  negative (natMod (suc n) (absoluteNat divisor))

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

setAt : {A : Set} → List A → Nat → A → List A
setAt [] _ value = []
setAt (_ ∷ xs) zero value = value ∷ xs
setAt (x ∷ xs) (suc n) value = x ∷ setAt xs n value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfInt : Bool → Int → Int → Int
IfInt true when-true when-false = when-true
IfInt false when-true when-false = when-false

countFrom : (Int → Bool) → Int → Nat → Nat
countFrom predicate start zero = zero
countFrom predicate start (suc count) with predicate start
... | true =
  suc (countFrom predicate (addInt start oneZ) count)
... | false =
  countFrom predicate (addInt start oneZ) count

numOf : (Int → Bool) → Int → Int → Int
numOf predicate lower upper =
  natToInt
    (countFrom predicate lower (toNat (subtractInt upper lower)))

module LinearProbingRemoveTheory
  (Key KeyM T : Set)
  (dummy : Key)
  (keym : Key → KeyM)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (hash : Key → Int)
  (bucket : Key → Int → Int)
  (size : T → Int)
  (entriesOf : T → List Key)
  (view : T → KeyM → Bool)
  (loc : T → KeyM → Int)
  where

  decide : (P : Set) → Dec P
  decide P with excludedMiddle P
  ... | left proof = yes proof
  ... | right refutation = no refutation

  eq : Key → Key → Set
  eq x y = keym x ≡ keym y

  neq : Key → Key → Set
  neq x y = Not (eq x y)

  equalKeyM : KeyM → KeyM → Bool
  equalKeyM x y with decide (x ≡ y)
  ... | yes _ = true
  ... | no _ = false

  update :
    {A : Set} →
    (KeyM → A) →
    KeyM →
    A →
    KeyM →
    A
  update old key value query with decide (query ≡ key)
  ... | yes _ = value
  ... | no _ = old query

  updateInt :
    (Int → Key) →
    Int →
    Key →
    Int →
    Key
  updateInt old index value query with intEqual query index
  ... | true = value
  ... | false = old query

  nthKey : List Key → Int → Key
  nthKey xs index = nthDefault dummy (toNat index) xs

  between : Int → Int → Int → Set
  between l j r =
    (l ≤Z j ∧ j <Z r)
    ∨ (r <Z l ∧ l ≤Z j)
    ∨ (j <Z r ∧ r <Z l)

  fc : List Key → Int → Bool
  fc xs i = equalKeyM (keym (nthKey xs i)) (keym dummy)

  numof : List Key → Int → Int → Int
  numof xs lower upper = numOf (fc xs) lower upper

  InRange : List Key → Int → Set
  InRange entries i =
    zeroZ ≤Z i ∧ i <Z lengthZ entries

  FunctionEqual :
    {A B : Set} →
    (A → B) →
    (A → B) →
    Set
  FunctionEqual f g = (x : _) → f x ≡ g x

  ArrayFunctionEqual :
    List Key →
    (Int → Key) →
    (Int → Key) →
    Set
  ArrayFunctionEqual entries f g =
    (index : Int) →
    InRange entries index →
    f index ≡ g index

  valid :
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  valid entries present location =
    Not (present (keym dummy) ≡ true)
    ∧
    ((i : Int) →
      InRange entries i →
      let x = nthKey entries i
      in
      neq x dummy →
      present (keym x) ≡ true ∧
      location (keym x) ≡ i)
    ∧
    (let n = lengthZ entries
     in
     (x : Key) →
     present (keym x) ≡ true →
     let i = location (keym x)
     in
     InRange entries i
     ∧ eq (nthKey entries i) x
     ∧
     ((j : Int) →
       InRange entries j →
       between (bucket x n) j i →
       neq (nthKey entries j) x ∧
       neq (nthKey entries j) dummy))

  StateInvariant :
    Int →
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  StateInvariant stateSize entries present location =
    zeroZ ≤Z stateSize
    ∧ stateSize <Z lengthZ entries
    ∧ addInt stateSize (numof entries zeroZ (lengthZ entries))
        ≡ lengthZ entries
    ∧ valid entries present location

  StateEqual : T → T → Set
  StateEqual a b =
    size a ≡ size b
    ∧ entriesOf a ≡ entriesOf b
    ∧ FunctionEqual (view a) (view b)
    ∧ FunctionEqual (loc a) (loc b)

  record Laws : Set where
    field
      hash-nonnegative :
        (k : Key) →
        zeroZ ≤Z hash k

      hash-respects-eq :
        (x y : Key) →
        eq x y →
        hash x ≡ hash y

      bucket-definition :
        (n : Int) →
        (k : Key) →
        zeroZ <Z n →
        bucket k n ≡ tmodInt (hash k) n

      bucket-range :
        (n : Int) →
        (k : Key) →
        zeroZ <Z n →
        zeroZ ≤Z bucket k n ∧ bucket k n <Z n

      state-invariant :
        (self : T) →
        StateInvariant
          (size self)
          (entriesOf self)
          (view self)
          (loc self)

      state-injective :
        (a b : T) →
        StateEqual a b →
        a ≡ b

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false with decide P
  ... | yes _ = when-true
  ... | no _ = when-false

  next : Int → Int → Int
  next n i =
    let i1 = addInt i oneZ
    in IfInt (intEqual i1 n) zeroZ i1

  ProbePrefix :
    Key →
    List Key →
    Int →
    Set
  ProbePrefix x entries i =
    (j : Int) →
    InRange entries j →
    between (bucket x (lengthZ entries)) j i →
    neq (nthKey entries j) x ∧
    neq (nthKey entries j) dummy

  UpdatedView : T → Key → KeyM → Bool
  UpdatedView h x =
    update (view h) (keym x) false

  NoDummyBetween :
    List Key →
    Int →
    Int →
    Set
  NoDummyBetween entries start finish =
    (k : Int) →
    InRange entries k →
    between start k finish →
    Not (k ≡ start) →
    neq (nthKey entries k) dummy

  MappedEntries :
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  MappedEntries entries present location =
    (k : Int) →
    InRange entries k →
    let x = nthKey entries k
    in
    neq x dummy →
    present (keym x) ≡ true ∧
    location (keym x) ≡ k

  LocatedAllowingHole :
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Int →
    Set
  LocatedAllowingHole entries present location hole =
    let n = lengthZ entries
    in
    (x : Key) →
    present (keym x) ≡ true →
    let k = location (keym x)
    in
    InRange entries k
    ∧ eq (nthKey entries k) x
    ∧
    ((l : Int) →
      InRange entries l →
      between (bucket x n) l k →
      neq (nthKey entries l) x
      ∧
      (neq (nthKey entries l) dummy
       ∨ (l ≡ hole ∧ between hole hole k)))

  CountAfterClear :
    List Key →
    Int →
    Int →
    Set
  CountAfterClear entries j nextIndex =
    IfSet
      (intLessOrEqual j nextIndex)
      (oneZ ≤Z
        addInt
          (numof entries nextIndex (lengthZ entries))
          (numof entries zeroZ j))
      (oneZ ≤Z numof entries nextIndex j)

  StateConstruction :
    Key →
    T →
    List Key →
    Set
  StateConstruction x h cleared =
    (location : KeyM → Int) →
    (newEntries : List Key) →
    length newEntries ≡ length cleared →
    length newEntries ≡ length cleared →
    (numof newEntries zeroZ (lengthZ newEntries)
      ≡ numof cleared zeroZ (lengthZ newEntries)
     ∧ valid newEntries (UpdatedView h x) location) →
    (h1 : T) →
    StateInvariant
      (subtractInt (size h) oneZ)
      newEntries
      (UpdatedView h x)
      location
    ∧
    ((FunctionEqual location (loc h1)
      ∧ FunctionEqual (UpdatedView h x) (view h1)
      ∧ newEntries ≡ entriesOf h1
      ∧ subtractInt (size h) oneZ ≡ size h1) →
      FunctionEqual (view h1) (UpdatedView h x))

  FoundFreeSlot :
    Key →
    T →
    Int →
    List Key →
    Int →
    Set
  FoundFreeSlot x h j cleared f0 =
    InRange cleared f0
    ∧ InRange cleared j
    ∧ InRange cleared j
    ∧ Not (j ≡ f0)
    ∧ eq (nthKey cleared j) dummy
    ∧ eq (nthKey cleared f0) dummy
    ∧ between j j f0
    ∧ NoDummyBetween cleared j f0
    ∧ Not (UpdatedView h x (keym dummy) ≡ true)
    ∧ MappedEntries cleared (UpdatedView h x) (loc h)
    ∧ LocatedAllowingHole cleared (UpdatedView h x) (loc h) j
    ∧ StateConstruction x h cleared

  ClearedLoop :
    Key →
    T →
    Int →
    List Key →
    Set
  ClearedLoop x h j cleared =
    let nextIndex = next (lengthZ (entriesOf h)) j
    in
    InRange cleared j
    ∧ InRange cleared nextIndex
    ∧ Not (nextIndex ≡ j)
    ∧ CountAfterClear cleared j nextIndex
    ∧ NoDummyBetween cleared j nextIndex
    ∧
    ((f0 : Int) →
      (InRange cleared f0
       ∧ Not (f0 ≡ j)
       ∧ eq (nthKey cleared f0) dummy
       ∧ NoDummyBetween cleared j f0) →
      FoundFreeSlot x h j cleared f0)

  RemoveAt :
    Key →
    T →
    Int →
    Set
  RemoveAt x h j =
    let oldEntries = entriesOf h
        cleared = setAt oldEntries (toNat j) dummy
    in
    InRange oldEntries j
    ∧
    (length cleared ≡ length oldEntries →
     length cleared ≡ length (entriesOf h) →
     ArrayFunctionEqual
       cleared
       (nthKey cleared)
       (updateInt (nthKey oldEntries) j dummy) →
     ClearedLoop x h j cleared)

  SearchResult :
    Key →
    T →
    Int →
    Set
  SearchResult x h j =
    let oldEntries = entriesOf h
        found = nthKey oldEntries j
    in
    InRange oldEntries j
    ∧
    ((neq found dummy ↔ Not (keym found ≡ keym dummy)) →
      IfProp
        (neq found dummy)
        (RemoveAt x h j)
        (FunctionEqual (view h) (UpdatedView h x)))

  RemoveConclusion :
    Key →
    T →
    Set
  RemoveConclusion x h =
    let entries = entriesOf h
    in
    (neq x dummy
     ∧
     (let n = lengthZ entries
      in zeroZ <Z n ∧ zeroZ <Z numof entries zeroZ n))
    ∧
    ((j : Int) →
      (InRange entries j
       ∧ (eq (nthKey entries j) dummy
          ∨ eq (nthKey entries j) x)
       ∧ ProbePrefix x entries j) →
      SearchResult x h j)

  RemoveVC :
    Laws →
    Key →
    T →
    Set
  RemoveVC laws x h =
    neq x dummy →
    RemoveConclusion x h

  remove-vc : Set
  remove-vc =
    (laws : Laws) →
    (x : Key) →
    (h : T) →
    RemoveVC laws x h
