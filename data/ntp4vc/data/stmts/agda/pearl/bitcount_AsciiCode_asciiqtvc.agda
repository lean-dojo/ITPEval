-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bitcount_AsciiCode_asciiqtvc: a 32-bit verification condition for
-- inserting the population-count parity bit while preserving the low 31 bits
-- and obtaining an even-population-count ASCII code. This file contains no proof.

{-# OPTIONS --safe #-}

module bitcount_AsciiCode_asciiqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _<N_
infixr 3 _∧_
infixr 2 _∨_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  leftCase  : A → A ∨ B
  rightCase : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

data _<N_ : Nat → Nat → Set where
  zero<successor :
    {n : Nat} →
    zero <N suc n
  successor<successor :
    {m n : Nat} →
    m <N n →
    suc m <N suc n

one two four eight sixteen : Nat
one = suc zero
two = suc one
four = two + two
eight = four + four
sixteen = eight + eight

twentySix twentySeven thirtyOne thirtyTwo : Nat
twentySix = sixteen + eight + two
twentySeven = twentySix + one
thirtyOne = sixteen + eight + four + two + one
thirtyTwo = sixteen + sixteen

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 5 _∷_

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []
replicate (suc n) value = value ∷ replicate n value

prefix : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
prefix {n = zero} (_ ∷ []) = []
prefix {n = suc n} (x ∷ xs) = x ∷ prefix xs

last : {A : Set} {n : Nat} → Vec A (suc n) → A
last {n = zero} (x ∷ []) = x
last {n = suc n} (_ ∷ xs) = last xs

bitOr : Bool → Bool → Bool
bitOr false y = y
bitOr true _ = true

orVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
orVec [] [] = []
orVec (x ∷ xs) (y ∷ ys) = bitOr x y ∷ orVec xs ys

bitValue : Bool → Nat
bitValue false = zero
bitValue true = one

unsignedVec : {n : Nat} → Vec Bool n → Nat
unsignedVec [] = zero
unsignedVec (bit ∷ bits) =
  bitValue bit + two * unsignedVec bits

countTrue : {n : Nat} → Vec Bool n → Nat
countTrue [] = zero
countTrue (false ∷ bits) = countTrue bits
countTrue (true ∷ bits) = suc (countTrue bits)

Even : Nat → Set
Even n = Exists Nat (λ k → n ≡ k + k)

Word32 : Set
Word32 = Vec Bool thirtyTwo

word31 word32 : Word32
word31 =
  true ∷ true ∷ true ∷ true ∷ true ∷
  replicate twentySeven false
word32 =
  false ∷ false ∷ false ∷ false ∷ false ∷ true ∷
  replicate twentySix false

unsigned : Word32 → Nat
unsigned = unsignedVec

signBit : Word32 → Bool
signBit = last

low31 : Word32 → Vec Bool thirtyOne
low31 = prefix

shiftOnce : {n : Nat} → Vec Bool (suc n) → Vec Bool (suc n)
shiftOnce bits = false ∷ prefix bits

shiftLeftNat : Word32 → Nat → Word32
shiftLeftNat bits zero = bits
shiftLeftNat bits (suc amount) =
  shiftLeftNat (shiftOnce bits) amount

shiftLeftWord : Word32 → Word32 → Word32
shiftLeftWord bits amount =
  shiftLeftNat bits (unsigned amount)

wordOr : Word32 → Word32 → Word32
wordOr = orVec

wordLess : Word32 → Word32 → Set
wordLess x y = unsigned x <N unsigned y

equalLow31 : Word32 → Word32 → Set
equalLow31 x y = low31 x ≡ low31 y

countLogic : Word32 → Nat
countLogic = countTrue

validAscii : Word32 → Set
validAscii bits = Even (countLogic bits)

AsciiVC : Word32 → Word32 → Set
AsciiVC b c =
  Not (signBit b ≡ true) →
  unsigned c ≡ countLogic b →
  (wordLess word31 word32 ∨ thirtyOne <N thirtyTwo) ∧
  (let maskbit = shiftLeftWord c word31
   in
   maskbit ≡ shiftLeftNat c thirtyOne →
   let code = wordOr b maskbit
   in
   equalLow31 code b ∧ validAscii code)

ascii'vc : Set
ascii'vc =
  (b c : Word32) →
  AsciiVC b c
