-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/linear_probing_LinearProbing_deleteqtvc: the verification condition
-- for deletion and key relocation in a linear-probing hash table, including
-- probe, array-update, counting, and validity obligations. This file contains no proof.

{-# OPTIONS --safe #-}

module linear_probing_LinearProbing_deleteqtvc where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

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

module LinearProbingDeleteTheory
  (Key KeyM : Set)
  (dummy : Key)
  (keym : Key → KeyM)
  (excludedMiddle : (P : Set) → P ∨ Not P)
  (hash : Key → Int)
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

  SameArray : List Key → List Key → Set
  SameArray leftEntries rightEntries =
    length leftEntries ≡ length rightEntries
    ∧
    ((i : Int) →
      InRange leftEntries i →
      nthKey leftEntries i ≡ nthKey rightEntries i)

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

  IfProp : (P : Set) → Set → Set → Set
  IfProp P when-true when-false with decide P
  ... | yes _ = when-true
  ... | no _ = when-false

  next : Int → Int → Int
  next n i =
    let i1 = addInt i oneZ
    in IfInt (intEqual i1 n) zeroZ i1

  loopDistance : Int → Int → Int → Int
  loopDistance n f0 i =
    IfInt
      (intLessOrEqual f0 i)
      (addInt (subtractInt n i) f0)
      (subtractInt f0 i)

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
    Int →
    Set
  LocatedAllowingHole entries present location hole scan =
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
       ∨ (l ≡ hole ∧ between hole scan k)))

  NextLoopState :
    Int →
    List Key →
    Int →
    Int →
    Int →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  NextLoopState oldI entries f0 j i1 present location =
    (zeroZ ≤Z loopDistance (lengthZ entries) f0 oldI
     ∧ loopDistance (lengthZ entries) f0 i1
       <Z loopDistance (lengthZ entries) f0 oldI)
    ∧ InRange entries f0
    ∧ InRange entries j
    ∧ InRange entries i1
    ∧ Not (j ≡ f0)
    ∧ eq (nthKey entries j) dummy
    ∧ eq (nthKey entries f0) dummy
    ∧ between j i1 f0
    ∧
    ((k : Int) →
      InRange entries k →
      between i1 k f0 →
      Not (k ≡ i1) →
      neq (nthKey entries k) dummy)
    ∧ Not (present (keym dummy) ≡ true)
    ∧ MappedEntries entries present location
    ∧ LocatedAllowingHole entries present location j i1

  MovedLoopState :
    List Key →
    List Key →
    Int →
    Int →
    Int →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  MovedLoopState oldEntries entries f0 oldI i1 present location =
    (zeroZ ≤Z loopDistance (lengthZ oldEntries) f0 oldI
     ∧ loopDistance (lengthZ entries) f0 i1
       <Z loopDistance (lengthZ oldEntries) f0 oldI)
    ∧ InRange entries f0
    ∧ InRange entries i1
    ∧ InRange entries i1
    ∧ Not (i1 ≡ f0)
    ∧ eq (nthKey entries i1) dummy
    ∧ eq (nthKey entries f0) dummy
    ∧ between i1 i1 f0
    ∧
    ((k : Int) →
      InRange entries k →
      between i1 k f0 →
      Not (k ≡ i1) →
      neq (nthKey entries k) dummy)
    ∧ Not (present (keym dummy) ≡ true)
    ∧ MappedEntries entries present location
    ∧ LocatedAllowingHole entries present location i1 i1

  CountAndValidityPreserved :
    List Key →
    List Key →
    (KeyM → Bool) →
    Set
  CountAndValidityPreserved oldEntries entries present =
    (location2 : KeyM → Int) →
    (entries2 : List Key) →
    length entries2 ≡ length entries →
    numof entries2 zeroZ (lengthZ entries2)
      ≡ numof entries zeroZ (lengthZ entries2)
    ∧ valid entries2 present location2 →
    numof entries2 zeroZ (lengthZ entries2)
      ≡ numof oldEntries zeroZ (lengthZ entries2)
    ∧ valid entries2 present location2

  RelocationBranch :
    List Key →
    Int →
    Int →
    Int →
    Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  RelocationBranch entries f0 j oldI xi present location =
    (entries1 : List Key) →
    SameArray entries1 entries →
    InRange entries j
    ∧
    (let replaced = setAt entries (toNat j) xi
     in
     length replaced ≡ length entries →
     ArrayFunctionEqual
       replaced
       (nthKey replaced)
       (updateInt (nthKey entries) j xi) →
     (entries2 : List Key) →
     SameArray entries2 replaced →
     let i1 = next (lengthZ entries) oldI
         cleared = setAt replaced (toNat i1) dummy
         movedLocation = update location (keym xi) j
     in
     InRange replaced i1
     ∧
     (length cleared ≡ length replaced →
      ArrayFunctionEqual
        cleared
        (nthKey cleared)
        (updateInt (nthKey replaced) i1 dummy) →
      MovedLoopState
        entries
        cleared
        f0
        oldI
        i1
        present
        movedLocation
      ∧ CountAndValidityPreserved entries cleared present))

  O2Condition : Int → Int → Int → Bool → Set
  O2Condition j r i1 o2 =
    IfSet
      (intLess j r)
      (o2 ≡ intLessOrEqual r i1)
      (o2 ≡ false)

  O3Condition : Int → Int → Int → Bool → Bool → Set
  O3Condition j r i1 o2 o3 =
    IfSet
      o2
      (o3 ≡ true)
      (Exists Bool
        (λ o4 →
          IfSet
            (intLess i1 j)
            (o4 ≡ intLess j r)
            (o4 ≡ false)
          ∧
          IfSet
            o4
            (o3 ≡ true)
            (IfSet
              (intLessOrEqual r i1)
              (o3 ≡ intLess i1 j)
              (o3 ≡ false))))

  OccupiedBranch :
    List Key →
    Int →
    Int →
    Int →
    Key →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  OccupiedBranch entries f0 j oldI xi present location =
    let n = lengthZ entries
        i1 = next n oldI
        r = bucket xi n
    in
    zeroZ <Z n
    ∧
    ((zeroZ ≤Z r ∧ r <Z n) →
      (o2 : Bool) →
      O2Condition j r i1 o2 →
      (o3 : Bool) →
      O3Condition j r i1 o2 o3 →
      IfSet
        o3
        (NextLoopState oldI entries f0 j i1 present location)
        (RelocationBranch
          entries f0 j oldI xi present location))

  DeleteConclusion :
    List Key →
    Int →
    Int →
    Int →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  DeleteConclusion entries f0 j oldI present location =
    let n = lengthZ entries
        i1 = next n oldI
        xi = nthKey entries i1
    in
    InRange entries i1
    ∧
    ((neq xi dummy ↔ Not (keym xi ≡ keym dummy)) →
      IfProp
        (neq xi dummy)
        (OccupiedBranch entries f0 j oldI xi present location)
        (valid entries present location))

  DeleteVC :
    Laws →
    Int →
    List Key →
    Int →
    Int →
    (KeyM → Bool) →
    (KeyM → Int) →
    Set
  DeleteVC laws f0 entries j oldI present location =
    InRange entries f0 →
    InRange entries j →
    InRange entries oldI →
    Not (j ≡ f0) →
    eq (nthKey entries j) dummy →
    eq (nthKey entries f0) dummy →
    between j oldI f0 →
    ((k : Int) →
      InRange entries k →
      between oldI k f0 →
      Not (k ≡ oldI) →
      neq (nthKey entries k) dummy) →
    Not (present (keym dummy) ≡ true) →
    MappedEntries entries present location →
    LocatedAllowingHole entries present location j oldI →
    DeleteConclusion entries f0 j oldI present location

  delete-vc : Set
  delete-vc =
    (laws : Laws) →
    (f0 : Int) →
    (entries : List Key) →
    (j oldI : Int) →
    (present : KeyM → Bool) →
    (location : KeyM → Int) →
    DeleteVC laws f0 entries j oldI present location
