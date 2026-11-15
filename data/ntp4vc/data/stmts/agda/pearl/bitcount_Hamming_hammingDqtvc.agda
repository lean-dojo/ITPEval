-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/bitcount_Hamming_hammingDqtvc: the 32-bit verification condition
-- relating the population count of a bitwise XOR to Hamming distance.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module bitcount_Hamming_hammingDqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 5 _∷_

data Vec (A : Set) : Nat → Set where
  []  : Vec A zero
  _∷_ : {n : Nat} → A → Vec A n → Vec A (suc n)

one two four eight sixteen thirtyTwo : Nat
one = suc zero
two = suc one
four = two + two
eight = four + four
sixteen = eight + eight
thirtyTwo = sixteen + sixteen

Word32 : Set
Word32 = Vec Bool thirtyTwo

xorBit : Bool → Bool → Bool
xorBit false y = y
xorBit true false = true
xorBit true true = false

xorVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
xorVec [] [] = []
xorVec (x ∷ xs) (y ∷ ys) =
  xorBit x y ∷ xorVec xs ys

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

hammingCount :
  {n : Nat} →
  Vec Bool n →
  Vec Bool n →
  Nat
hammingCount [] [] = zero
hammingCount (false ∷ xs) (false ∷ ys) =
  hammingCount xs ys
hammingCount (false ∷ xs) (true ∷ ys) =
  suc (hammingCount xs ys)
hammingCount (true ∷ xs) (false ∷ ys) =
  suc (hammingCount xs ys)
hammingCount (true ∷ xs) (true ∷ ys) =
  hammingCount xs ys

unsigned : Word32 → Nat
unsigned = unsignedVec

countLogic : Word32 → Nat
countLogic = countTrue

hammingDLogic : Word32 → Word32 → Nat
hammingDLogic = hammingCount

hammingD'vc : Set
hammingD'vc =
  (result a b : Word32) →
  unsigned result ≡ countLogic (xorVec a b) →
  unsigned result ≡ hammingDLogic a b
