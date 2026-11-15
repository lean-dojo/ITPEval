-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/string_search_BadShiftTable_make_tableqtvc: the verification condition
-- for constructing a byte-pattern bad-shift table while preserving its loop
-- invariants and final shift bounds. This file contains no proof.

{-# OPTIONS --safe #-}

module string_search_BadShiftTable_make_tableqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Sigma using (Σ)

infix 4 _≤Z_ _<Z_ _≢_
infixr 5 _∷V_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≢_ : {A : Set} → A → A → Set
x ≢ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

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

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateVec : {A : Set} → (n : Nat) → A → Vec A n
replicateVec zero value = []V
replicateVec (suc n) value = value ∷V replicateVec n value

andBool : Bool → Bool → Bool
andBool false _ = false
andBool true value = value

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

vecEqual : {n : Nat} → Vec Bool n → Vec Bool n → Bool
vecEqual []V []V = true
vecEqual (x ∷V xs) (y ∷V ys) =
  andBool (boolEqual x y) (vecEqual xs ys)

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + (suc (suc zero)) * unsignedNat bits

lastBit : {n : Nat} → Vec Bool (suc n) → Bool
lastBit {zero} (bit ∷V []V) = bit
lastBit {suc n} (_ ∷V bits) = lastBit bits

nthVec : {A : Set} {n : Nat} → A → Nat → Vec A n → A
nthVec default index []V = default
nthVec default zero (x ∷V xs) = x
nthVec default (suc index) (_ ∷V xs) =
  nthVec default index xs

Byte Word63 : Set
Byte = Vec Bool 8
Word63 = Vec Bool 63

zeroByte : Byte
zeroByte = replicateVec 8 false

zeroWord63 : Word63
zeroWord63 = replicateVec 63 false

signed63 : Word63 → Int
signed63 bits with lastBit bits
... | false = pos (unsignedNat bits)
... | true =
  subtractInt
    (pos (unsignedNat bits))
    (pos 9223372036854775808)

min63 max63 : Int
min63 = negsuc 4611686018427387903
max63 = pos 4611686018427387903

int63InBounds : Int → Set
int63InBounds value =
  min63 ≤Z value ∧ value ≤Z max63

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) =
  nthDefault default n xs

nthByte : List Byte → Int → Byte
nthByte pat index =
  nthDefault zeroByte (toNat index) pat

ByteMap : Set
ByteMap = Byte → Maybe Word63

emptyMap : ByteMap
emptyMap _ = nothing

MapEqual : ByteMap → ByteMap → Set
MapEqual left right =
  (key : Byte) → left key ≡ right key

HasKey : Byte → ByteMap → Set
HasKey key table =
  Σ Word63 (λ value → table key ≡ just value)

lookupTotal : ByteMap → Byte → Word63
lookupTotal table key with table key
... | nothing = zeroWord63
... | just value = value

insertMap : Byte → Word63 → ByteMap → ByteMap
insertMap key value old query with vecEqual query key
... | true = just value
... | false = old query

module BadShiftTableTheory
  (T : Set → Set)
  (toMap : T Word63 → ByteMap)
  where

  PrefixPresent :
    List Byte →
    ByteMap →
    Int →
    Set
  PrefixPresent pat table upper =
    (j : Int) →
    (zeroZ ≤Z j ∧ j <Z upper) →
    HasKey (nthByte pat j) table

  ShiftBounds :
    Int →
    ByteMap →
    Set
  ShiftBounds patternLength table =
    (character : Byte) →
    HasKey character table →
    oneZ ≤Z signed63 (lookupTotal table character)
    ∧
    signed63 (lookupTotal table character) ≤Z
      addInt patternLength oneZ

  NoRecentOccurrence :
    Int →
    List Byte →
    ByteMap →
    Int →
    Set
  NoRecentOccurrence patternLength pat table upper =
    (character : Byte) →
    HasKey character table →
    (j : Int) →
    (subtractInt
      patternLength
      (signed63 (lookupTotal table character)) <Z j
     ∧ j <Z upper) →
    nthByte pat j ≢ character

  LoopInvariant :
    Int →
    List Byte →
    ByteMap →
    Int →
    Set
  LoopInvariant patternLength pat table upper =
    PrefixPresent pat table upper
    ∧
    ShiftBounds patternLength table
    ∧
    NoRecentOccurrence patternLength pat table upper

  FinalNoOccurrence :
    List Byte →
    ByteMap →
    Set
  FinalNoOccurrence pat table =
    (character : Byte) →
    HasKey character table →
    (j : Int) →
    (oneZ ≤Z j
     ∧ j <Z signed63 (lookupTotal table character)) →
    nthByte pat (subtractInt (lengthZ pat) j) ≢
      character

  FinalInvariant :
    List Byte →
    ByteMap →
    Set
  FinalInvariant pat table =
    PrefixPresent pat table (lengthZ pat)
    ∧
    ShiftBounds (lengthZ pat) table
    ∧
    FinalNoOccurrence pat table

  UpdateObligation :
    Int →
    List Byte →
    T Word63 →
    Word63 →
    Word63 →
    Set
  UpdateObligation patternLength pat sht2 i o2 =
    (zeroZ ≤Z signed63 i
     ∧ signed63 i <Z lengthZ pat)
    ∧
    ((sht3 : T Word63) →
      MapEqual
        (toMap sht3)
        (insertMap
          (nthByte pat (signed63 i))
          o2
          (toMap sht2)) →
      LoopInvariant
        patternLength
        pat
        (toMap sht3)
        (addInt (signed63 i) oneZ))

  IterationResult :
    Int →
    List Byte →
    T Word63 →
    Word63 →
    Set
  IterationResult patternLength pat sht2 i =
    int63InBounds
      (subtractInt patternLength (signed63 i))
    ∧
    ((o2 : Word63) →
      signed63 o2 ≡
        subtractInt patternLength (signed63 i) →
      UpdateObligation patternLength pat sht2 i o2)

  IterationObligation :
    Int →
    List Byte →
    Word63 →
    T Word63 →
    Set
  IterationObligation patternLength pat o1 sht2 =
    (i : Word63) →
    let i1 = signed63 i
    in
    ((zeroZ ≤Z i1 ∧ i1 ≤Z signed63 o1)
     ∧
     LoopInvariant patternLength pat (toMap sht2) i1) →
    IterationResult patternLength pat sht2 i

  LoopPackage :
    Int →
    List Byte →
    Word63 →
    T Word63 →
    Set
  LoopPackage patternLength pat o1 sht2 =
    IterationObligation patternLength pat o1 sht2
    ∧
    (LoopInvariant
      patternLength
      pat
      (toMap sht2)
      (addInt (signed63 o1) oneZ) →
     FinalInvariant pat (toMap sht2))

  PositiveRangeCase :
    Int →
    List Byte →
    T Word63 →
    Word63 →
    Set
  PositiveRangeCase patternLength pat sht1 o1 =
    zeroZ ≤Z addInt (signed63 o1) oneZ →
    LoopInvariant patternLength pat (toMap sht1) zeroZ
    ∧
    ((sht2 : T Word63) →
      LoopPackage patternLength pat o1 sht2)

  NegativeRangeCase :
    List Byte →
    T Word63 →
    Word63 →
    Set
  NegativeRangeCase pat sht1 o1 =
    addInt (signed63 o1) oneZ <Z zeroZ →
    FinalInvariant pat (toMap sht1)

  MakeTableConclusion :
    Word63 →
    List Byte →
    T Word63 →
    Set
  MakeTableConclusion m pat sht1 =
    int63InBounds (subtractInt (signed63 m) oneZ)
    ∧
    ((o1 : Word63) →
      signed63 o1 ≡ subtractInt (signed63 m) oneZ →
      PositiveRangeCase (signed63 m) pat sht1 o1
      ∧
      NegativeRangeCase pat sht1 o1)

  make-table-vc : Set
  make-table-vc =
    (m : Word63) →
    (pat : List Byte) →
    (sht1 : T Word63) →
    signed63 m ≡ lengthZ pat →
    zeroZ ≤Z lengthZ pat →
    MapEqual (toMap sht1) emptyMap →
    MakeTableConclusion m pat sht1
