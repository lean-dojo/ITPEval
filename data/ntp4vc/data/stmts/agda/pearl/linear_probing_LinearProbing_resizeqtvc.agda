-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linear_probing_LinearProbing_resizeqtvc: the verification condition
-- for resizing a linear-probing hash table while preserving probing, counting,
-- validity, and state-construction obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module linear_probing_LinearProbing_resizeqtvc where

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

module LinearProbingResizeTheory
  (Key KeyM T : Set)
  (dummy : Key)
  (stateWitness : T)
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

  InRangeBound : Int → Int → Set
  InRangeBound bound i =
    zeroZ ≤Z i ∧ i <Z bound

  InRange : List Key → Int → Set
  InRange entries i =
    InRangeBound (lengthZ entries) i

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
     InRangeBound n i
     ∧ eq (nthKey entries i) x
     ∧
     ((j : Int) →
       InRangeBound n j →
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

  constantZero : KeyM → Int
  constantZero _ = zeroZ

  AllDummy : List Key → Int → Set
  AllDummy entries bound =
    (i : Int) →
    InRangeBound bound i →
    nthKey entries i ≡ dummy

  ProbePrefix :
    Key →
    List Key →
    Int →
    Int →
    Set
  ProbePrefix x entries bound finish =
    (k : Int) →
    InRangeBound bound k →
    between (bucket x bound) k finish →
    neq (nthKey entries k) x ∧
    neq (nthKey entries k) dummy

  MappedEntries :
    T →
    List Key →
    (KeyM → Int) →
    Int →
    Set
  MappedEntries h entries location bound =
    (j : Int) →
    InRangeBound bound j →
    neq (nthKey entries j) dummy →
    view h (keym (nthKey entries j)) ≡ true
    ∧ location (keym (nthKey entries j)) ≡ j

  LocatedByCutoff :
    T →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Set
  LocatedByCutoff h entries location cutoff bound =
    (x : Key) →
    view h (keym x) ≡ true →
    IfProp
      (loc h (keym x) <Z cutoff)
      (let j = location (keym x)
       in
       InRangeBound bound j
       ∧ eq (nthKey entries j) x
       ∧ ProbePrefix x entries bound j)
      ((j : Int) →
       InRangeBound bound j →
       neq (nthKey entries j) x)

  TableStateAtCutoff :
    T →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Set
  TableStateAtCutoff h entries location cutoff bound =
    numof entries zeroZ bound
      ≡ subtractInt
          (addInt
            (numof (entriesOf h) zeroZ cutoff)
            bound)
          cutoff
    ∧ MappedEntries h entries location bound
    ∧ LocatedByCutoff h entries location cutoff bound

  IterationInvariant :
    T →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Int →
    Set
  IterationInvariant h entries location i last bound =
    (zeroZ ≤Z i ∧ i ≤Z last)
    ∧ TableStateAtCutoff h entries location i bound

  UpdatedEntries : List Key → Int → Key → List Key
  UpdatedEntries entries j x =
    setAt entries (toNat j) x

  UpdatedLocation :
    (KeyM → Int) →
    Key →
    Int →
    KeyM →
    Int
  UpdatedLocation location x j =
    update location (keym x) j

  SearchCandidate :
    Key →
    List Key →
    Int →
    Set
  SearchCandidate x entries j =
    InRange entries j
    ∧ (eq (nthKey entries j) dummy
       ∨ eq (nthKey entries j) x)
    ∧ ProbePrefix x entries (lengthZ entries) j

  InsertContinuation :
    T →
    Key →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Int →
    Set
  InsertContinuation h x entries location i bound j =
    let updated = UpdatedEntries entries j x
        updatedLocation = UpdatedLocation location x j
    in
    InRange entries j
    ∧
    (length updated ≡ length entries →
     ArrayFunctionEqual
       updated
       (nthKey updated)
       (updateInt (nthKey entries) j x) →
     TableStateAtCutoff
       h
       updated
       updatedLocation
       (addInt i oneZ)
       bound)

  NonDummyIteration :
    T →
    Key →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Set
  NonDummyIteration h x entries location i bound =
    (neq x dummy
     ∧
     (zeroZ <Z lengthZ entries
      ∧ zeroZ <Z numof entries zeroZ (lengthZ entries)))
    ∧
    ((j : Int) →
      SearchCandidate x entries j →
      InsertContinuation h x entries location i bound j)

  IterationStep :
    T →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Set
  IterationStep h entries location i bound =
    let oldEntries = entriesOf h
        x = nthKey oldEntries i
    in
    InRange oldEntries i
    ∧
    ((neq x dummy ↔ Not (keym x ≡ keym dummy)) →
     IfProp
       (neq x dummy)
       (NonDummyIteration h x entries location i bound)
       (TableStateAtCutoff
         h
         entries
         location
         (addInt i oneZ)
         bound))

  FinalConstruction :
    T →
    List Key →
    (KeyM → Int) →
    Set
  FinalConstruction h newEntries newLocation =
    (h1 : T) →
    StateInvariant
      (size h)
      newEntries
      (view h)
      newLocation
    ∧
    ((FunctionEqual newLocation (loc h1)
      ∧ FunctionEqual (view h) (view h1)
      ∧ newEntries ≡ entriesOf h1
      ∧ size h ≡ size h1) →
      lengthZ (entriesOf h1)
        ≡ multiplyInt twoZ (lengthZ (entriesOf h)))

  LoopPackage :
    T →
    List Key →
    (KeyM → Int) →
    Int →
    Int →
    Set
  LoopPackage h entries location last bound =
    ((i : Int) →
      IterationInvariant h entries location i last bound →
      IterationStep h entries location i bound)
    ∧
    (TableStateAtCutoff
      h
      entries
      location
      (addInt last oneZ)
      bound →
      FinalConstruction h entries location)

  InitializedRun :
    T →
    List Key →
    Int →
    Int →
    Set
  InitializedRun h initialEntries last bound =
    TableStateAtCutoff
      h
      initialEntries
      constantZero
      zeroZ
      bound
    ∧
    ((location : KeyM → Int) →
      (working : List Key) →
      length working ≡ length initialEntries →
      LoopPackage h working location last bound)

  ResizeForArray :
    T →
    List Key →
    Int →
    Int →
    Set
  ResizeForArray h initialEntries oldLength newLength =
    let last = subtractInt oldLength oneZ
    in
    (zeroZ ≤Z addInt last oneZ →
      InitializedRun h initialEntries last newLength)
    ∧
    (addInt last oneZ <Z zeroZ →
      FinalConstruction h initialEntries constantZero)

  ResizeVC :
    Laws →
    T →
    Set
  ResizeVC laws h =
    let oldLength = lengthZ (entriesOf h)
        newLength = multiplyInt twoZ oldLength
    in
    zeroZ ≤Z newLength
    ∧
    ((initialEntries : List Key) →
      (AllDummy initialEntries newLength
       ∧ lengthZ initialEntries ≡ newLength) →
      ResizeForArray
        h
        initialEntries
        oldLength
        newLength)

  resize-vc : Set
  resize-vc =
    (laws : Laws) →
    (h : T) →
    ResizeVC laws h
