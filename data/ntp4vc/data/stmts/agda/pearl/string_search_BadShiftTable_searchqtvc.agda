-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/string_search_BadShiftTable_searchqtvc: the bad-shift string-search
-- verification condition preserving the search invariant, variant decrease,
-- and success-or-no-occurrence postcondition. This file contains no proof.

{-# OPTIONS --safe #-}

module string_search_BadShiftTable_searchqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

andBool : Bool → Bool → Bool
andBool false _ = false
andBool true value = value

boolEqual : Bool → Bool → Bool
boolEqual false false = true
boolEqual false true = false
boolEqual true false = false
boolEqual true true = true

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

zeroZ oneZ minusOneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lengthZ : {A : Set} → List A → Int
lengthZ xs = natToInt (length xs)

take : {A : Set} → Nat → List A → List A
take zero _ = []
take (suc _) [] = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : {A : Set} → Nat → List A → List A
drop zero xs = xs
drop (suc _) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

substring : {A : Set} → List A → Int → Int → List A
substring xs start count =
  take (toNat count) (drop (toNat start) xs)

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateVec : {A : Set} → (n : Nat) → A → Vec A n
replicateVec zero value = []V
replicateVec (suc n) value = value ∷V replicateVec n value

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
nthByte xs index =
  nthDefault zeroByte (toNat index) xs

listByteEqual : List Byte → List Byte → Bool
listByteEqual [] [] = true
listByteEqual [] (_ ∷ _) = false
listByteEqual (_ ∷ _) [] = false
listByteEqual (x ∷ xs) (y ∷ ys) =
  andBool (vecEqual x y) (listByteEqual xs ys)

ByteMap : Set
ByteMap = Byte → Maybe Word63

hasKey : ByteMap → Byte → Bool
hasKey table key with table key
... | nothing = false
... | just _ = true

HasKey : Byte → ByteMap → Set
HasKey key table =
  hasKey table key ≡ true

optionThe : Maybe Word63 → Word63
optionThe nothing = zeroWord63
optionThe (just value) = value

lookupTotal : ByteMap → Byte → Word63
lookupTotal table key =
  optionThe (table key)

record BadShiftTable : Set where
  constructor badShiftTable
  field
    pat    : List Byte
    shifts : ByteMap

open BadShiftTable

BadShiftInvariant : BadShiftTable → Set
BadShiftInvariant bst =
  ((j : Int) →
    (character : Byte) →
    (zeroZ ≤Z j ∧ j <Z lengthZ (BadShiftTable.pat bst)) →
    character ≡ nthByte (BadShiftTable.pat bst) j →
    HasKey character (shifts bst))
  ∧
  ((character : Byte) →
    HasKey character (shifts bst) →
    oneZ ≤Z signed63 (lookupTotal (shifts bst) character)
    ∧
    signed63 (lookupTotal (shifts bst) character) ≤Z
      addInt (lengthZ (BadShiftTable.pat bst)) oneZ)
  ∧
  ((character : Byte) →
    HasKey character (shifts bst) →
    (j : Int) →
    (oneZ ≤Z j
     ∧ j <Z signed63 (lookupTotal (shifts bst) character)) →
    nthByte
      (BadShiftTable.pat bst)
      (subtractInt (lengthZ (BadShiftTable.pat bst)) j)
      ≢ character)

matchesBool : List Byte → List Byte → Int → Bool
matchesBool pat text position =
  andBool
    (intLessOrEqual zeroZ position)
    (andBool
      (intLessOrEqual
        position
        (subtractInt (lengthZ text) (lengthZ pat)))
      (listByteEqual
        (substring text position (lengthZ pat))
        pat))

Matches : List Byte → List Byte → Int → Set
Matches pat text position =
  matchesBool pat text position ≡ true

NoMatchBefore :
  List Byte →
  List Byte →
  Int →
  Int →
  Int →
  Set
NoMatchBefore pat text patternLength textLength upper =
  (j : Int) →
  (zeroZ ≤Z j ∧ j <Z upper) →
  j ≤Z subtractInt textLength patternLength →
  substring text j patternLength ≢ pat

SearchInvariant :
  List Byte →
  List Byte →
  Int →
  Int →
  Int →
  Set
SearchInvariant pat text patternLength textLength index =
  (zeroZ ≤Z index ∧ index ≤Z textLength)
  ∧
  NoMatchBefore pat text patternLength textLength index

InitialInvariant :
  List Byte →
  List Byte →
  Int →
  Int →
  Set
InitialInvariant pat text patternLength textLength =
  (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z textLength)
  ∧
  NoMatchBefore pat text patternLength textLength zeroZ

SearchPost :
  List Byte →
  List Byte →
  Int →
  Set
SearchPost pat text result =
  (minusOneZ ≤Z result
   ∧ result ≤Z subtractInt (lengthZ text) (lengthZ pat))
  ∧
  IfSet
    (intEqual result minusOneZ)
    ((j : Int) → Not (Matches pat text j))
    (Matches pat text result)

ShiftAvailability :
  BadShiftTable →
  Byte →
  Int →
  Set
ShiftAvailability bst character patternLength =
  IfSet
    (hasKey (shifts bst) character)
    (HasKey character (shifts bst))
    (int63InBounds (addInt patternLength oneZ))

ShiftValue :
  BadShiftTable →
  Byte →
  Int →
  Word63 →
  Set
ShiftValue bst character patternLength value =
  IfSet
    (hasKey (shifts bst) character)
    (value ≡ lookupTotal (shifts bst) character
     ∧ value ≡ optionThe ((shifts bst) character))
    (signed63 value ≡ addInt patternLength oneZ)

AfterShift :
  List Byte →
  List Byte →
  Int →
  Int →
  Word63 →
  Word63 →
  Set
AfterShift pat text patternLength textLength index shift =
  int63InBounds (addInt (signed63 index) (signed63 shift))
  ∧
  ((next : Word63) →
    signed63 next ≡
      addInt (signed63 index) (signed63 shift) →
    (zeroZ ≤Z
      subtractInt
        (subtractInt textLength patternLength)
        (signed63 index)
     ∧
     subtractInt
       (subtractInt textLength patternLength)
       (signed63 next)
       <Z
       subtractInt
         (subtractInt textLength patternLength)
         (signed63 index))
    ∧
    SearchInvariant
      pat text patternLength textLength (signed63 next))

ReadCharacter :
  BadShiftTable →
  List Byte →
  List Byte →
  Int →
  Int →
  Word63 →
  Word63 →
  Set
ReadCharacter bst pat text patternLength textLength index offset =
  (zeroZ ≤Z signed63 offset
   ∧ signed63 offset <Z lengthZ text)
  ∧
  let character = nthByte text (signed63 offset)
  in
  ShiftAvailability bst character patternLength
  ∧
  ((shift : Word63) →
    ShiftValue bst character patternLength shift →
    AfterShift
      pat text patternLength textLength index shift)

Advance :
  BadShiftTable →
  List Byte →
  List Byte →
  Int →
  Int →
  Word63 →
  Word63 →
  Set
Advance bst pat text patternLength textLength index m =
  int63InBounds (addInt (signed63 index) (signed63 m))
  ∧
  ((offset : Word63) →
    signed63 offset ≡
      addInt (signed63 index) (signed63 m) →
    ReadCharacter
      bst pat text patternLength textLength index offset)

AfterFailedOccurs :
  BadShiftTable →
  List Byte →
  List Byte →
  Int →
  Int →
  Word63 →
  Word63 →
  Set
AfterFailedOccurs bst pat text patternLength textLength index m =
  int63InBounds (subtractInt textLength patternLength)
  ∧
  ((limit : Word63) →
    signed63 limit ≡ subtractInt textLength patternLength →
    (signed63 index ≡ signed63 limit → index ≡ limit) →
    IfSet
      (vecEqual index limit)
      (SearchPost (BadShiftTable.pat bst) text minusOneZ)
      (Advance
        bst pat text patternLength textLength index m))

GuardTrue :
  BadShiftTable →
  List Byte →
  List Byte →
  Int →
  Int →
  Word63 →
  Word63 →
  Set
GuardTrue bst pat text patternLength textLength index m =
  (zeroZ ≤Z signed63 index
   ∧
   signed63 index ≤Z
     subtractInt (lengthZ text) (lengthZ pat))
  ∧
  IfSet
    (matchesBool pat text (signed63 index))
    (SearchPost
      (BadShiftTable.pat bst)
      text
      (signed63 index))
    (AfterFailedOccurs
      bst pat text patternLength textLength index m)

Iteration :
  BadShiftTable →
  List Byte →
  List Byte →
  Int →
  Int →
  Word63 →
  Word63 →
  Set
Iteration bst pat text patternLength textLength index m =
  int63InBounds (subtractInt textLength patternLength)
  ∧
  ((limit : Word63) →
    signed63 limit ≡ subtractInt textLength patternLength →
    IfSet
      (intLessOrEqual (signed63 index) (signed63 limit))
      (GuardTrue
        bst pat text patternLength textLength index m)
      (SearchPost (BadShiftTable.pat bst) text minusOneZ))

SearchBody :
  BadShiftTable →
  List Byte →
  List Byte →
  Word63 →
  Word63 →
  Set
SearchBody bst pat text m n =
  InitialInvariant
    pat text (signed63 m) (signed63 n)
  ∧
  ((index : Word63) →
    SearchInvariant
      pat text (signed63 m) (signed63 n) (signed63 index) →
    Iteration
      bst pat text (signed63 m) (signed63 n) index m)

search-vc : Set
search-vc =
  (bst : BadShiftTable) →
  BadShiftInvariant bst →
  (text : List Byte) →
  lengthZ (BadShiftTable.pat bst) ≤Z lengthZ text →
  let pat = BadShiftTable.pat bst
  in
  (m : Word63) →
  (signed63 m ≡ lengthZ pat ∧ zeroZ ≤Z lengthZ pat) →
  (n : Word63) →
  (signed63 n ≡ lengthZ text ∧ zeroZ ≤Z lengthZ text) →
  SearchBody bst pat text m n
