-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bitcount_BitCounting32_countqtvc: the 32-bit population-count
-- verification condition for its five bit-manipulation steps and final
-- equality with the number of set bits. This file contains no proof.

{-# OPTIONS --safe #-}

module bitcount_BitCounting32_countqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 5 _∷_
infixr 4 _++_
infixr 3 _∧_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []
replicate (suc n) value = value ∷ replicate n value

_++_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

snoc : {A : Set} {n : Nat} → Vec A n → A → Vec A (suc n)
snoc [] y = y ∷ []
snoc (x ∷ xs) y = x ∷ snoc xs y

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

andVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
andVec [] [] = []
andVec (x ∷ xs) (y ∷ ys) = andBit x y ∷ andVec xs ys

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
addWithCarry carry [] [] = []
addWithCarry carry (x ∷ xs) (y ∷ ys) =
  sumBit carry x y ∷
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
subtractWithBorrow borrow [] [] = []
subtractWithBorrow borrow (x ∷ xs) (y ∷ ys) =
  differenceBit borrow x y ∷
  subtractWithBorrow (borrowBit borrow x y) xs ys

shiftRightOnce :
  {n : Nat} →
  Vec Bool (suc n) →
  Vec Bool (suc n)
shiftRightOnce (_ ∷ xs) = snoc xs false

shiftRightNat :
  {n : Nat} →
  Vec Bool (suc n) →
  Nat →
  Vec Bool (suc n)
shiftRightNat bits zero = bits
shiftRightNat bits (suc amount) =
  shiftRightNat (shiftRightOnce bits) amount

bitValue : Bool → Nat
bitValue false = zero
bitValue true = suc zero

unsignedVec : {n : Nat} → Vec Bool n → Nat
unsignedVec [] = zero
unsignedVec (bit ∷ bits) =
  bitValue bit + (suc (suc zero)) * unsignedVec bits

countTrue : {n : Nat} → Vec Bool n → Nat
countTrue [] = zero
countTrue (false ∷ bits) = countTrue bits
countTrue (true ∷ bits) = suc (countTrue bits)

one two four eight sixteen : Nat
one = suc zero
two = suc one
four = two + two
eight = four + four
sixteen = eight + eight

twentySeven twentyEight twentyNine thirty thirtyOne thirtyTwo : Nat
twentySeven = sixteen + eight + two + one
twentyEight = sixteen + eight + four
twentyNine = twentyEight + one
thirty = twentyEight + two
thirtyOne = thirty + one
thirtyTwo = sixteen + sixteen

Word32 : Set
Word32 = Vec Bool thirtyTwo

wordOne wordTwo wordFour wordEight wordSixteen : Word32
wordOne =
  true ∷ replicate thirtyOne false
wordTwo =
  false ∷ true ∷ replicate thirty false
wordFour =
  false ∷ false ∷ true ∷ replicate twentyNine false
wordEight =
  false ∷ false ∷ false ∷ true ∷ replicate twentyEight false
wordSixteen =
  false ∷ false ∷ false ∷ false ∷ true ∷
  replicate twentySeven false

Byte : Set
Byte = Vec Bool eight

zeroByte mask55Byte mask33Byte mask0FByte mask3FByte : Byte
zeroByte =
  replicate eight false
mask55Byte =
  true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ true ∷ false ∷ []
mask33Byte =
  true ∷ true ∷ false ∷ false ∷ true ∷ true ∷ false ∷ false ∷ []
mask0FByte =
  true ∷ true ∷ true ∷ true ∷ false ∷ false ∷ false ∷ false ∷ []
mask3FByte =
  true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ false ∷ false ∷ []

fourBytes : Byte → Word32
fourBytes byte =
  byte ++ (byte ++ (byte ++ byte))

mask55 mask33 mask0F mask63 : Word32
mask55 = fourBytes mask55Byte
mask33 = fourBytes mask33Byte
mask0F = fourBytes mask0FByte
mask63 =
  mask3FByte ++ (zeroByte ++ (zeroByte ++ zeroByte))

wordAnd : Word32 → Word32 → Word32
wordAnd = andVec

wordAdd : Word32 → Word32 → Word32
wordAdd = addWithCarry false

wordSub : Word32 → Word32 → Word32
wordSub = subtractWithBorrow false

unsigned : Word32 → Nat
unsigned = unsignedVec

wordShiftRight : Word32 → Word32 → Word32
wordShiftRight bits amount =
  shiftRightNat bits (unsigned amount)

step0 : Word32 → Word32 → Set
step0 n x1 =
  x1 ≡
  wordSub n (wordAnd (wordShiftRight n wordOne) mask55)

step1 : Word32 → Word32 → Set
step1 x1 x2 =
  x2 ≡
  wordAdd
    (wordAnd x1 mask33)
    (wordAnd (wordShiftRight x1 wordTwo) mask33)

step2 : Word32 → Word32 → Set
step2 x2 x3 =
  x3 ≡
  wordAnd
    (wordAdd x2 (wordShiftRight x2 wordFour))
    mask0F

step3 : Word32 → Word32 → Set
step3 x3 x4 =
  x4 ≡ wordAdd x3 (wordShiftRight x3 wordEight)

step4 : Word32 → Word32 → Set
step4 x4 x5 =
  x5 ≡ wordAdd x4 (wordShiftRight x4 wordSixteen)

numOfBits : Word32 → Nat
numOfBits = countTrue

countLogic : Word32 → Nat
countLogic = numOfBits

CountVC : Word32 → Set
CountVC n =
  let
    x1 =
      wordSub n (wordAnd (wordShiftRight n wordOne) mask55)
    x2 =
      wordAdd
        (wordAnd x1 mask33)
        (wordAnd (wordShiftRight x1 wordTwo) mask33)
    x3 =
      wordAnd
        (wordAdd x2 (wordShiftRight x2 wordFour))
        mask0F
    x4 =
      wordAdd x3 (wordShiftRight x3 wordEight)
    x5 =
      wordAdd x4 (wordShiftRight x4 wordSixteen)
    result =
      unsigned (wordAnd x5 mask63)
  in
  step0 n x1 ∧
  step1 x1 x2 ∧
  step2 x2 x3 ∧
  step3 x3 x4 ∧
  step4 x4 x5 ∧
  (result ≡ numOfBits n → result ≡ countLogic n)

count'vc : Set
count'vc =
  (n : Word32) →
  CountVC n
