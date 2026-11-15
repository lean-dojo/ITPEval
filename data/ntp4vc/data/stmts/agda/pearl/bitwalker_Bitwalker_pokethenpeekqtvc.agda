-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bitwalker_Bitwalker_pokethenpeekqtvc: the bitwalker verification
-- condition that a successful bounded poke followed by a peek returns the
-- written 64-bit value. This file contains no proof.

{-# OPTIONS --safe #-}

module bitwalker_Bitwalker_pokethenpeekqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_ _↔_
infixr 5 _∷V_
infixr 4 _++V_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

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

Word8 Word32 Word64 : Set
Word8 = Vec Bool 8
Word32 = Vec Bool 32
Word64 = Vec Bool 64

zero8 : Word8
zero8 = replicate 8 false

zero64 one64 : Word64
zero64 = natToVec 64 0
one64 = natToVec 64 1

bitAt : {n : Nat} → Vec Bool n → Int → Bool
bitAt bits (pos index) = nthVec false index bits
bitAt bits (negsuc _) = false

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

zeroZ oneZ minusOneZ minusTwoZ sixtyFourZ limit32Z : Int
zeroZ = pos 0
oneZ = pos 1
minusOneZ = negsuc 0
minusTwoZ = negsuc 1
sixtyFourZ = pos 64
limit32Z = pos 4294967296

endPosition : Word32 → Word32 → Int
endPosition start len = addInt (unsignedZ start) (unsignedZ len)

LoadedLowBits :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
LoadedLowBits addr start len value =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z unsignedZ len) →
  bitAt value i ≡
    nth8-stream
      addr
      (subtractInt
        (subtractInt (endPosition start len) i)
        oneZ)

ClearedAbove : Word32 → Word64 → Set
ClearedAbove len value =
  (i : Int) →
  (unsignedZ len ≤Z i ∧ i <Z sixtyFourZ) →
  bitAt value i ≡ false

PeekConditions :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
PeekConditions addr len start value =
  (addressBits addr <Z endPosition start len → value ≡ zero64)
  ∧
  (endPosition start len ≤Z addressBits addr →
    LoadedLowBits addr start len value ∧
    ClearedAbove len value)

PrefixUnchanged :
  List Word8 →
  List Word8 →
  Word32 →
  Set
PrefixUnchanged addr addr1 start =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z unsignedZ start) →
  nth8-stream addr i ≡ nth8-stream addr1 i

WrittenSegment :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
WrittenSegment addr1 len start value =
  (i : Int) →
  (unsignedZ start ≤Z i ∧ i <Z endPosition start len) →
  nth8-stream addr1 i ≡
    bitAt
      value
      (addInt
        (subtractInt
          (subtractInt (unsignedZ len) i)
          oneZ)
        (unsignedZ start))

SuffixUnchanged :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Set
SuffixUnchanged addr addr1 len start =
  (i : Int) →
  (endPosition start len ≤Z i ∧ i <Z addressBits addr1) →
  nth8-stream addr1 i ≡ nth8-stream addr i

AllBitsUnchanged : List Word8 → List Word8 → Set
AllBitsUnchanged addr addr1 =
  (i : Int) →
  (zeroZ ≤Z i ∧ i <Z addressBits addr1) →
  nth8-stream addr1 i ≡ nth8-stream addr i

PokeSuccessRelations :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
PokeSuccessRelations addr addr1 len start value =
  PrefixUnchanged addr addr1 start ∧
  WrittenSegment addr1 len start value ∧
  SuffixUnchanged addr addr1 len start

ResultConditions :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Set
ResultConditions addr addr1 len start value res =
  (minusTwoZ ≤Z res ∧ res ≤Z zeroZ)
  ∧
  ((res ≡ minusOneZ) ↔
    (addressBits addr1 <Z endPosition start len))
  ∧
  ((res ≡ minusTwoZ) ↔
    (unsignedZ (maxvalue len) ≤Z unsignedZ value ∧
     endPosition start len ≤Z addressBits addr1))
  ∧
  ((res ≡ zeroZ) ↔
    (unsignedZ value <Z unsignedZ (maxvalue len) ∧
     endPosition start len ≤Z addressBits addr1))
  ∧
  (res ≡ zeroZ →
    PokeSuccessRelations addr addr1 len start value)

PostPokeBounds :
  List Word8 →
  Word32 →
  Word32 →
  Set
PostPokeBounds addr1 len start =
  unsignedZ len ≤Z sixtyFourZ
  ∧
  endPosition start len <Z limit32Z
  ∧
  addressBits addr1 <Z limit32Z

PeekReturnsWrittenValue :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
PeekReturnsWrittenValue addr1 len start value =
  (peek-result : Word64) →
  PeekConditions addr1 len start peek-result →
  peek-result ≡ value

PokeThenPeekForResult :
  List Word8 →
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Int →
  Set
PokeThenPeekForResult addr addr1 len start value poke-result =
  ResultConditions addr addr1 len start value poke-result →
  PostPokeBounds addr1 len start
  ∧
  PeekReturnsWrittenValue addr1 len start value

PokeThenPeekConclusion :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
PokeThenPeekConclusion addr len start value =
  unsignedZ len <Z sixtyFourZ
  ∧
  endPosition start len <Z limit32Z
  ∧
  addressBits addr <Z limit32Z
  ∧
  ((addr1 : List Word8) →
    length addr1 ≡ length addr →
    (poke-result : Int) →
    PokeThenPeekForResult
      addr
      addr1
      len
      start
      value
      poke-result)

PokeThenPeekVC :
  List Word8 →
  Word32 →
  Word32 →
  Word64 →
  Set
PokeThenPeekVC addr len start value =
  addressBits addr <Z limit32Z →
  zeroZ ≤Z unsignedZ len →
  unsignedZ len <Z sixtyFourZ →
  endPosition start len ≤Z addressBits addr →
  unsignedZ value <Z unsignedZ (maxvalue len) →
  PokeThenPeekConclusion addr len start value

pokethenpeek'vc : Set
pokethenpeek'vc =
  (addr : List Word8) →
  (len start : Word32) →
  (value : Word64) →
  PokeThenPeekVC addr len start value
