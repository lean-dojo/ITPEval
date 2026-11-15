-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linear_probing_LinearProbing_addqtvc: the verification condition for
-- adding a key to a linear-probing hash table, including resize, probing,
-- invariant preservation, and view-update obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module linear_probing_LinearProbing_addqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

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

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

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

module LinearProbingTheory
  (Key KeyM T : Set)
  (dummy : Key)
  (stateWitness : T)
  (keym : Key → KeyM)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (hash : Key → Int)
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
    (zeroZ ≤Z index ∧ index <Z lengthZ entries) →
    f index ≡ g index

  bucket : Key → Int → Int
  bucket k n = tmodInt (hash k) n

  between : Int → Int → Int → Set
  between l j r =
    (l ≤Z j ∧ j <Z r)
    ∨ (r <Z l ∧ l ≤Z j)
    ∨ (j <Z r ∧ r <Z l)

  fc : List Key → Int → Bool
  fc xs i = equalKeyM (keym (nthKey xs i)) (keym dummy)

  numof : List Key → Int → Int → Int
  numof xs lower upper = numOf (fc xs) lower upper

  valid :
    List Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  valid entries present location =
    Not (present (keym dummy) ≡ true)
    ∧
    ((i : Int) →
      (zeroZ ≤Z i ∧ i <Z lengthZ entries) →
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
     (zeroZ ≤Z i ∧ i <Z n)
     ∧ eq (nthKey entries i) x
     ∧
     ((j : Int) →
       (zeroZ ≤Z j ∧ j <Z n) →
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

  open Laws

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false with decide P
  ... | yes _ = when-true
  ... | no _ = when-false

  ProbePrefix :
    Key →
    List Key →
    Int →
    Set
  ProbePrefix x entries i =
    (j : Int) →
    (zeroZ ≤Z j ∧ j <Z lengthZ entries) →
    between (bucket x (lengthZ entries)) j i →
    neq (nthKey entries j) x ∧
    neq (nthKey entries j) dummy

  UpdatedView :
    T →
    Key →
    KeyM →
    Bool
  UpdatedView h x =
    update (view h) (keym x) true

  UpdatedLoc :
    T →
    Key →
    Int →
    KeyM →
    Int
  UpdatedLoc h x i =
    update (loc h) (keym x) i

  InsertedData :
    T →
    Int →
    Key →
    List Key
  InsertedData h i x =
    setAt (entriesOf h) (toNat i) x

  NewKeyBranch :
    Key →
    T →
    T →
    Int →
    Set
  NewKeyBranch x original h1 i =
    (zeroZ ≤Z i ∧ i <Z lengthZ (entriesOf h1))
    ∧
    (length (InsertedData h1 i x) ≡ length (entriesOf h1) →
     length (InsertedData h1 i x) ≡ length (entriesOf h1) →
     ArrayFunctionEqual
       (InsertedData h1 i x)
       (nthKey (InsertedData h1 i x))
       (updateInt (nthKey (entriesOf h1)) i x) →
     (h2 : T) →
     StateInvariant
       (addInt (size h1) oneZ)
       (InsertedData h1 i x)
       (UpdatedView h1 x)
       (UpdatedLoc h1 x i)
     ∧
     (FunctionEqual (UpdatedLoc h1 x i) (loc h2)
      ∧ FunctionEqual (UpdatedView h1 x) (view h2)
      ∧ InsertedData h1 i x ≡ entriesOf h2
      ∧ addInt (size h1) oneZ ≡ size h2 →
      FunctionEqual (view h2) (UpdatedView original x)))

  ExistingKeyBranch :
    Key →
    T →
    T →
    Int →
    Set
  ExistingKeyBranch x original h1 i =
    (h2 : T) →
    StateInvariant
      (size h1)
      (entriesOf h1)
      (UpdatedView h1 x)
      (UpdatedLoc h1 x i)
    ∧
    (FunctionEqual (UpdatedLoc h1 x i) (loc h2)
     ∧ FunctionEqual (UpdatedView h1 x) (view h2)
     ∧ entriesOf h1 ≡ entriesOf h2
     ∧ size h1 ≡ size h2 →
     FunctionEqual (view h2) (UpdatedView original x))

  ProbeStep :
    Key →
    T →
    T →
    Int →
    Set
  ProbeStep x original h1 i =
    let o2 = dummy
        o3 = entriesOf h1
        o4 = nthKey o3 i
    in
    (zeroZ ≤Z i ∧ i <Z lengthZ o3)
    ∧
    ((eq o4 o2 ↔ keym o4 ≡ keym o2) →
     IfProp
       (eq o4 o2)
       (NewKeyBranch x original h1 i)
       (ExistingKeyBranch x original h1 i))

  SearchObligation :
    Key →
    T →
    T →
    Set
  SearchObligation x original h1 =
    let entries = entriesOf h1
        n = lengthZ entries
    in
    (neq x dummy ∧ (zeroZ <Z n ∧ zeroZ <Z numof entries zeroZ n))
    ∧
    ((i : Int) →
      ((zeroZ ≤Z i ∧ i <Z lengthZ entries)
       ∧ (eq (nthKey entries i) dummy
          ∨ eq (nthKey entries i) x)
       ∧ ProbePrefix x entries i) →
      ProbeStep x original h1 i)

  ResizeObligation : T → Set
  ResizeObligation h =
    IfSet
      (intLessOrEqual
        (lengthZ (entriesOf h))
        (multiplyInt twoZ (addInt (size h) oneZ)))
      ((h1 : T) →
        (FunctionEqual (view h) (view h1) ∧ size h ≡ size h1) →
        lengthZ (entriesOf h1) ≡
          multiplyInt twoZ (lengthZ (entriesOf h)) →
        addInt (size h1) oneZ <Z lengthZ (entriesOf h1))
      (addInt (size h) oneZ <Z lengthZ (entriesOf h))

  AddVC :
    Laws →
    Key →
    T →
    Set
  AddVC laws x h =
    neq x dummy →
    ResizeObligation h
    ∧
    ((h1 : T) →
      (FunctionEqual (view h) (view h1) ∧ size h ≡ size h1) →
      addInt (size h1) oneZ <Z lengthZ (entriesOf h1) →
      SearchObligation x h h1)

  add-vc : Set
  add-vc =
    (laws : Laws) →
    (x : Key) →
    (h : T) →
    AddVC laws x h
