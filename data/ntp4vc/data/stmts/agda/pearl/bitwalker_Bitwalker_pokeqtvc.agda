-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bitwalker_Bitwalker_pokeqtvc: the bitwalker poke verification
-- condition for writing a bounded segment of a 64-bit value into a byte
-- stream while maintaining its bounds and loop invariants. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module bitwalker_Bitwalker_pokeqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_ _↔_
infixr 5 _∷V_
infixr 4 _++V_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

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

difference : Nat → Nat → Int
difference zero zero = pos zero
difference (suc m) zero = pos (suc m)
difference zero (suc n) = negsuc n
difference (suc m) (suc n) = difference m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = difference m (suc n)
addInt (negsuc m) (pos n) = difference n (suc m)
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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

natSubtract : Nat → Nat → Nat
natSubtract n zero = n
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

div8Nat : Nat → Nat
div8Nat zero = zero
div8Nat (suc zero) = zero
div8Nat (suc (suc zero)) = zero
div8Nat (suc (suc (suc zero))) = zero
div8Nat (suc (suc (suc (suc zero)))) = zero
div8Nat (suc (suc (suc (suc (suc zero))))) = zero
div8Nat (suc (suc (suc (suc (suc (suc zero)))))) = zero
div8Nat (suc (suc (suc (suc (suc (suc (suc zero))))))) = zero
div8Nat (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) =
  suc (div8Nat n)

mod8Nat : Nat → Nat
mod8Nat zero = zero
mod8Nat (suc zero) = 1
mod8Nat (suc (suc zero)) = 2
mod8Nat (suc (suc (suc zero))) = 3
mod8Nat (suc (suc (suc (suc zero)))) = 4
mod8Nat (suc (suc (suc (suc (suc zero))))) = 5
mod8Nat (suc (suc (suc (suc (suc (suc zero)))))) = 6
mod8Nat (suc (suc (suc (suc (suc (suc (suc zero))))))) = 7
mod8Nat (suc (suc (suc (suc (suc (suc (suc (suc n)))))))) =
  mod8Nat n

ceilDiv8 : Nat → Nat
ceilDiv8 n = div8Nat (n + 7)

div8Int : Int → Int
div8Int (pos n) = pos (div8Nat n)
div8Int (negsuc n) = negative (ceilDiv8 (suc n))

mod8Int : Int → Int
mod8Int (pos n) = pos (mod8Nat n)
mod8Int (negsuc n) =
  pos (natSubtract (8 * ceilDiv8 (suc n)) (suc n))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

data Vec (A : Set) : Nat → Set where
  []V   : Vec A zero
  _∷V_  : {n : Nat} → A → Vec A n → Vec A (suc n)

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []V
replicate (suc n) value = value ∷V replicate n value

_++V_ :
  {A : Set} {m n : Nat} →
  Vec A m →
  Vec A n →
  Vec A (m + n)
[]V ++V ys = ys
(x ∷V xs) ++V ys = x ∷V (xs ++V ys)

nthVec : {A : Set} {n : Nat} → A → Nat → Vec A n → A
nthVec default index []V = default
nthVec default zero (x ∷V xs) = x
nthVec default (suc index) (_ ∷V xs) = nthVec default index xs

notBit : Bool → Bool
notBit false = true
notBit true = false

orBit : Bool → Bool → Bool
orBit false y = y
orBit true _ = true

xorBit : Bool → Bool → Bool
xorBit false y = y
xorBit true false = true
xorBit true true = false

andBit : Bool → Bool → Bool
andBit false _ = false
andBit true y = y

sumBit : Bool → Bool → Bool → Bool
sumBit carry x y = xorBit (xorBit x y) carry

carryBit : Bool → Bool → Bool → Bool
carryBit carry x y =
  orBit (andBit x y) (andBit carry (xorBit x y))

addWithCarry :
  {n : Nat} →
  Bool →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
addWithCarry carry []V []V = []V
addWithCarry carry (x ∷V xs) (y ∷V ys) =
  sumBit carry x y ∷V
  addWithCarry (carryBit carry x y) xs ys

differenceBit : Bool → Bool → Bool → Bool
differenceBit borrow x y = xorBit (xorBit x y) borrow

borrowBit : Bool → Bool → Bool → Bool
borrowBit borrow x y =
  orBit
    (andBit (notBit x) y)
    (andBit borrow (notBit (xorBit x y)))

subtractWithBorrow :
  {n : Nat} →
  Bool →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
subtractWithBorrow borrow []V []V = []V
subtractWithBorrow borrow (x ∷V xs) (y ∷V ys) =
  differenceBit borrow x y ∷V
  subtractWithBorrow (borrowBit borrow x y) xs ys

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

unsignedZ : {n : Nat} → Vec Bool n → Int
unsignedZ bits = pos (unsignedNat bits)

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

lowBit : Nat → Bool
lowBit zero = false
lowBit (suc zero) = true
lowBit (suc (suc n)) = lowBit n

natToVec : (width value : Nat) → Vec Bool width
natToVec zero value = []V
natToVec (suc width) value =
  lowBit value ∷V natToVec width (half value)

prefix : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
prefix {n = zero} (_ ∷V []V) = []V
prefix {n = suc n} (x ∷V xs) = x ∷V prefix xs

shiftLeftOnce :
  {n : Nat} →
  Vec Bool (suc n) →
  Vec Bool (suc n)
shiftLeftOnce bits = false ∷V prefix bits

shiftLeftNat :
  {n : Nat} →
  Vec Bool (suc n) →
  Nat →
  Vec Bool (suc n)
shiftLeftNat bits zero = bits
shiftLeftNat bits (suc amount) =
  shiftLeftNat (shiftLeftOnce bits) amount

Word8 Word32 Word64 Word128 : Set
Word8 = Vec Bool 8
Word32 = Vec Bool 32
Word64 = Vec Bool 64
Word128 = Vec Bool 128

zero8 : Word8
zero8 = replicate 8 false

zero32 one32 sixtyFour32 max32 : Word32
zero32 = natToVec 32 0
one32 = natToVec 32 1
sixtyFour32 = natToVec 32 64
max32 = natToVec 32 4294967295

one64 : Word64
one64 = natToVec 64 1

addWord :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
addWord = addWithCarry false

subWord :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
subWord = subtractWithBorrow false

wordLessBool :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Bool
wordLessBool x y = natLess (unsignedNat x) (unsignedNat y)

wordLeBool :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Bool
wordLeBool x y = natLessOrEqual (unsignedNat x) (unsignedNat y)

wordLe :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Set
wordLe x y = wordLeBool x y ≡ true

bitAt : {n : Nat} → Vec Bool n → Int → Bool
bitAt bits index = nthVec false (toNat index) bits

zeroExtend32to128 : Word32 → Word128
zeroExtend32to128 bits = bits ++V replicate 96 false

max32In128 : Word128
max32In128 = zeroExtend32to128 max32

nth8-stream : List Word8 → Int → Bool
nth8-stream stream position =
  let
    byte =
      nthDefault
        zero8
        (toNat (div8Int position))
        stream
    index = subtractInt (pos 7) (mod8Int position)
  in
  bitAt byte index

maxvalue : Word32 → Word64
maxvalue len =
  shiftLeftNat one64 (unsignedNat len)

addressBits : List Word8 → Int
addressBits addr = multiplyInt (pos 8) (pos (length addr))

zeroZ oneZ minusOneZ minusTwoZ sixtyThreeZ sixtyFourZ limit32Z : Int
zeroZ = pos 0
oneZ = pos 1
minusOneZ = negsuc 0
minusTwoZ = negsuc 1
sixtyThreeZ = pos 63
sixtyFourZ = pos 64
limit32Z = pos 4294967296

endPosition : Word32 → Word32 → Int
endPosition start len = addInt (unsignedZ start) (unsignedZ len)

wideGuard : Word32 → Word32 → Set
wideGuard x y =
  addInt (unsignedZ x) (unsignedZ y) <Z limit32Z
  ∨
  wordLe
    (addWord
      (zeroExtend32to128 x)
      (zeroExtend32to128 y))
    max32In128

PrefixUnchanged :
  List Word8 →
  List Word8 →
  Word32 →
  Set
PrefixUnchanged addr addr1 start =
  (j : Int) →
  (zeroZ ≤Z j ∧ j <Z unsignedZ start) →
  nth8-stream addr j ≡ nth8-stream addr1 j

WrittenSegment :
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
WrittenSegment addr1 start len i value =
  (j : Int) →
  (unsignedZ start ≤Z j
    ∧
    j <Z addInt (unsignedZ start) (unsignedZ i)) →
  nth8-stream addr1 j ≡
    bitAt
      value
      (addInt
        (subtractInt
          (subtractInt (unsignedZ len) j)
          oneZ)
        (unsignedZ start))

SuffixUnchanged :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Set
SuffixUnchanged addr addr1 start i =
  (j : Int) →
  (addInt (unsignedZ start) (unsignedZ i) ≤Z j
    ∧
    j <Z addressBits addr1) →
  nth8-stream addr1 j ≡ nth8-stream addr j

LoopInvariant :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
LoopInvariant addr addr1 start len i value =
  (zeroZ ≤Z unsignedZ i ∧ unsignedZ i ≤Z unsignedZ len)
  ∧
  PrefixUnchanged addr addr1 start
  ∧
  WrittenSegment addr1 start len i value
  ∧
  SuffixUnchanged addr addr1 start i

InitialInvariant :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
InitialInvariant addr start len value =
  (zeroZ ≤Z zeroZ ∧ zeroZ ≤Z unsignedZ len)
  ∧
  WrittenSegment addr start len zero32 value

UpdateRelation :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
UpdateRelation addr1 addr2 start lstart i value =
  ((i1 : Int) →
    (zeroZ ≤Z i1 ∧ i1 <Z addressBits addr2) →
    i1 ≠ unsignedZ (addWord start i) →
    nth8-stream addr2 i1 ≡ nth8-stream addr1 i1)
  ∧
  nth8-stream addr2 (unsignedZ (addWord start i)) ≡
    bitAt
      value
      (subtractInt
        sixtyThreeZ
        (unsignedZ (addWord lstart i)))

IncrementConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
IncrementConclusion addr addr2 start len i value =
  let next = addWord i one32
  in
  (zeroZ ≤Z subtractInt (unsignedZ len) (unsignedZ i)
    ∧
    subtractInt (unsignedZ len) (unsignedZ next) <Z
      subtractInt (unsignedZ len) (unsignedZ i))
  ∧
  LoopInvariant addr addr2 start len next value

UpdatedStreamConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
UpdatedStreamConclusion addr addr2 start len i value =
  wideGuard i one32
  ∧
  (unsignedZ (addWord i one32)
    ≡
    addInt (unsignedZ i) oneZ →
    IncrementConclusion addr addr2 start len i value)

UpdateConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
UpdateConclusion addr addr1 start len lstart i value =
  (addr2 : List Word8) →
  length addr2 ≡ length addr1 →
  UpdateRelation addr1 addr2 start lstart i value →
  UpdatedStreamConclusion addr addr2 start len i value

StartAddressConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
StartAddressConclusion addr addr1 start len lstart i value =
  (addressBits addr1 <Z limit32Z
    ∧
    unsignedZ (addWord start i) <Z addressBits addr1)
  ∧
  UpdateConclusion addr addr1 start len lstart i value

ShiftAddressConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
ShiftAddressConclusion addr addr1 start len lstart i value =
  unsignedZ (addWord lstart i) <Z sixtyFourZ
  ∧
  wideGuard start i
  ∧
  (unsignedZ (addWord start i)
    ≡
    addInt (unsignedZ start) (unsignedZ i) →
    StartAddressConclusion addr addr1 start len lstart i value)

ContinueConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
ContinueConclusion addr addr1 start len lstart i value =
  wideGuard lstart i
  ∧
  (unsignedZ (addWord lstart i)
    ≡
    addInt (unsignedZ lstart) (unsignedZ i) →
    ShiftAddressConclusion addr addr1 start len lstart i value)

FinishConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
FinishConclusion addr addr1 start len value =
  (minusTwoZ ≤Z zeroZ ∧ zeroZ ≤Z zeroZ)
  ∧
  ((zeroZ ≡ minusOneZ) ↔
    (addressBits addr1 <Z endPosition start len))
  ∧
  ((zeroZ ≡ minusTwoZ) ↔
    (unsignedZ (maxvalue len) ≤Z unsignedZ value
      ∧
      endPosition start len ≤Z addressBits addr1))
  ∧
  (unsignedZ value <Z unsignedZ (maxvalue len)
    ∧
    endPosition start len ≤Z addressBits addr1)
  ∧
  PrefixUnchanged addr addr1 start
  ∧
  WrittenSegment addr1 start len len value
  ∧
  SuffixUnchanged addr addr1 start len

IterationConclusion :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word32 →
  Word32 →
  Word64 →
  Set
IterationConclusion addr addr1 start len lstart i value =
  IfSet
    (wordLessBool i len)
    (ContinueConclusion addr addr1 start len lstart i value)
    (FinishConclusion addr addr1 start len value)

LongEnoughConclusion :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
LongEnoughConclusion addr start len value =
  (unsignedZ len ≤Z sixtyFourZ ∨ wordLe len sixtyFour32)
  ∧
  (let lstart = subWord sixtyFour32 len
   in
   unsignedZ lstart
     ≡
     subtractInt sixtyFourZ (unsignedZ len) →
   InitialInvariant addr start len value
   ∧
   ((i : Word32) →
     (addr1 : List Word8) →
     length addr1 ≡ length addr →
     LoopInvariant addr addr1 start len i value →
     IterationConclusion addr addr1 start len lstart i value))

AddressTooShortConclusion :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
AddressTooShortConclusion addr start len value =
  (minusTwoZ ≤Z minusOneZ ∧ minusOneZ ≤Z zeroZ)
  ∧
  addressBits addr <Z endPosition start len
  ∧
  ((minusOneZ ≡ minusTwoZ) ↔
    (unsignedZ (maxvalue len) ≤Z unsignedZ value
      ∧
      endPosition start len ≤Z addressBits addr))
  ∧
  ((minusOneZ ≡ zeroZ) ↔
    (unsignedZ value <Z unsignedZ (maxvalue len)
      ∧
      endPosition start len ≤Z addressBits addr))
  ∧
  (minusOneZ ≡ zeroZ →
    WrittenSegment addr start len len value)

ValueTooLargeConclusion :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
ValueTooLargeConclusion addr start len value =
  (minusTwoZ ≤Z minusTwoZ ∧ minusTwoZ ≤Z zeroZ)
  ∧
  ((minusTwoZ ≡ minusOneZ) ↔
    (addressBits addr <Z endPosition start len))
  ∧
  (unsignedZ (maxvalue len) ≤Z unsignedZ value
    ∧
    endPosition start len ≤Z addressBits addr)
  ∧
  ((minusTwoZ ≡ zeroZ) ↔
    (unsignedZ value <Z unsignedZ (maxvalue len)
      ∧
      endPosition start len ≤Z addressBits addr))
  ∧
  (minusTwoZ ≡ zeroZ →
    WrittenSegment addr start len len value)

PokeBody :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
PokeBody addr start len value =
  IfSet
    (intLess
      (addressBits addr)
      (unsignedZ (addWord start len)))
    (AddressTooShortConclusion addr start len value)
    (IfSet
      (wordLeBool (maxvalue len) value)
      (ValueTooLargeConclusion addr start len value)
      (LongEnoughConclusion addr start len value))

PokeVC :
  Word32 →
  Word32 →
  List Word8 →
  Word64 →
  Set
PokeVC len start addr value =
  unsignedZ len <Z sixtyFourZ →
  endPosition start len <Z limit32Z →
  addressBits addr <Z limit32Z →
  wideGuard start len
  ∧
  (unsignedZ (addWord start len)
    ≡
    endPosition start len →
    PokeBody addr start len value)

poke'vc : Set
poke'vc =
  (len start : Word32) →
  (addr : List Word8) →
  (value : Word64) →
  PokeVC len start addr value
