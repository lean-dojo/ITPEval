-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bitwalker_Bitwalker_poke_8bitqtvc: the 8-bit bitwalker poke
-- verification condition, which updates one mirrored bit and preserves every
-- other bit in both bitvector- and integer-indexed views. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module bitwalker_Bitwalker_poke_8bitqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

data ⊤ : Set where
  tt : ⊤

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

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []V
replicate (suc n) value = value ∷V replicate n value

nthVec : {A : Set} {n : Nat} → A → Nat → Vec A n → A
nthVec default index []V = default
nthVec default zero (x ∷V xs) = x
nthVec default (suc index) (_ ∷V xs) = nthVec default index xs

notBit : Bool → Bool
notBit false = true
notBit true = false

andBit : Bool → Bool → Bool
andBit false _ = false
andBit true y = y

orBit : Bool → Bool → Bool
orBit false y = y
orBit true _ = true

xorBit : Bool → Bool → Bool
xorBit false y = y
xorBit true false = true
xorBit true true = false

notVec : {n : Nat} → Vec Bool n → Vec Bool n
notVec []V = []V
notVec (x ∷V xs) = notBit x ∷V notVec xs

andVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
andVec []V []V = []V
andVec (x ∷V xs) (y ∷V ys) =
  andBit x y ∷V andVec xs ys

orVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
orVec []V []V = []V
orVec (x ∷V xs) (y ∷V ys) =
  orBit x y ∷V orVec xs ys

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

Word8 Word32 Word64 : Set
Word8 = Vec Bool 8
Word32 = Vec Bool 32
Word64 = Vec Bool 64

one8 seven8 : Word8
one8 = natToVec 8 1
seven8 = natToVec 8 7

seven32 eight32 : Word32
seven32 = natToVec 32 7
eight32 = natToVec 32 8

one64 : Word64
one64 = natToVec 64 1

subWord :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
subWord = subtractWithBorrow false

wordLe :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Set
wordLe x y =
  natLessOrEqual (unsignedNat x) (unsignedNat y) ≡ true

wordLess :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Set
wordLess x y =
  natLess (unsignedNat x) (unsignedNat y) ≡ true

truncate32To8 : Word32 → Word8
truncate32To8 value = natToVec 8 (unsignedNat value)

bitAtNat : {n : Nat} → Vec Bool n → Nat → Bool
bitAtNat bits index = nthVec false index bits

bitAtZ : {n : Nat} → Vec Bool n → Int → Bool
bitAtZ bits index = bitAtNat bits (toNat index)

maxvalue : Word32 → Word64
maxvalue len =
  shiftLeftNat one64 (unsignedNat len)

zeroZ sevenZ eightZ : Int
zeroZ = pos 0
sevenZ = pos 7
eightZ = pos 8

BitvectorPokePost :
  Bool →
  Word8 →
  Word8 →
  Word32 →
  Set
BitvectorPokePost flag result byte left1 =
  ((i : Word32) →
    wordLess i eight32 →
    i ≠ subWord seven32 left1 →
    bitAtNat result (unsignedNat (truncate32To8 i)) ≡
    bitAtNat byte (unsignedNat (truncate32To8 i)))
  ∧
  bitAtNat
    result
    (unsignedNat (subWord seven8 (truncate32To8 left1)))
    ≡ flag

IntegerPokePost :
  Bool →
  Word8 →
  Word8 →
  Word32 →
  Set
IntegerPokePost flag result byte left1 =
  ((i : Int) →
    (zeroZ ≤Z i ∧ i <Z eightZ) →
    i ≠ subtractInt sevenZ (unsignedZ left1) →
    bitAtZ result i ≡ bitAtZ byte i)
  ∧
  bitAtZ result (subtractInt sevenZ (unsignedZ left1)) ≡ flag

Poke8Body :
  Word32 →
  Bool →
  Word8 →
  Set
Poke8Body left1 flag byte =
  let o1 = truncate32To8 left1
  in
  ((unsignedZ o1 ≤Z sevenZ
    ∨
    wordLe o1 seven8)
   ∧
   (let o2 = subWord seven8 o1
    in
    unsignedZ o2 ≡ subtractInt sevenZ (unsignedZ o1) →
    let mask = shiftLeftNat one8 (unsignedNat o2)
    in
    IfSet flag ⊤ ⊤
    ∧
    ((result : Word8) →
      IfSet
        flag
        (result ≡ orVec byte mask)
        (result ≡ andVec byte (notVec mask)) →
      BitvectorPokePost flag result byte left1)))
  ∧
  ((result : Word8) →
    BitvectorPokePost flag result byte left1 →
    IntegerPokePost flag result byte left1)

poke-8bit'vc : Set
poke-8bit'vc =
  (left1 : Word32) →
  (flag : Bool) →
  (byte : Word8) →
  unsignedZ left1 <Z eightZ →
  Poke8Body left1 flag byte
