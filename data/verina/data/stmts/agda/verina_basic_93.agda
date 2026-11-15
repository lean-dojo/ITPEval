-- Statement-only formalization of VERINA corpus artifact verina_basic_93,
-- catalog title "SwapBitvectors": a deterministic UInt8-pair program swaps
-- its two inputs using three bitwise XOR operations and is connected to its
-- full correctness contract. This file contains no proof.

{-# OPTIONS --safe #-}

module VerinaBasic93 where

open import Agda.Builtin.Equality using (_≡_)

infixr 3 _∧_
infixr 4 _,_
infixr 5 _×_
infix 4 _≢_

record Top : Set where
  constructor top

data Bottom : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first-conjunct : A
    second-conjunct : B

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    pairFirst : A
    pairSecond : B

open _×_ public

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → Bottom

data Bit : Set where
  zeroBit : Bit
  oneBit : Bit

data UInt8 : Set where
  byte :
    (bit0 bit1 bit2 bit3 bit4 bit5 bit6 bit7 : Bit) →
    UInt8

xorBit : Bit → Bit → Bit
xorBit zeroBit zeroBit = zeroBit
xorBit zeroBit oneBit = oneBit
xorBit oneBit zeroBit = oneBit
xorBit oneBit oneBit = zeroBit

xorUInt8 : UInt8 → UInt8 → UInt8
xorUInt8
  (byte x0 x1 x2 x3 x4 x5 x6 x7)
  (byte y0 y1 y2 y3 y4 y5 y6 y7) =
  byte
    (xorBit x0 y0)
    (xorBit x1 y1)
    (xorBit x2 y2)
    (xorBit x3 y3)
    (xorBit x4 y4)
    (xorBit x5 y5)
    (xorBit x6 y6)
    (xorBit x7 y7)

SwapBitvectors-precond : UInt8 → UInt8 → Set
SwapBitvectors-precond X Y = Top

SwapBitvectors :
  (X Y : UInt8) →
  SwapBitvectors-precond X Y →
  UInt8 × UInt8
SwapBitvectors X Y h-precond =
  let temp = xorUInt8 X Y
      newY = xorUInt8 temp Y
      newX = xorUInt8 temp newY
  in newX , newY

SwapBitvectors-postcond :
  (X Y : UInt8) →
  (result : UInt8 × UInt8) →
  SwapBitvectors-precond X Y →
  Set
SwapBitvectors-postcond X Y result h-precond =
  (pairFirst result ≡ Y) ∧
  (pairSecond result ≡ X) ∧
  (X ≢ Y →
    (pairFirst result ≢ X) ∧
    (pairSecond result ≢ Y))

SwapBitvectors-spec-satisfied : Set
SwapBitvectors-spec-satisfied =
  (X Y : UInt8) →
  (h-precond : SwapBitvectors-precond X Y) →
  SwapBitvectors-postcond
    X
    Y
    (SwapBitvectors X Y h-precond)
    h-precond
