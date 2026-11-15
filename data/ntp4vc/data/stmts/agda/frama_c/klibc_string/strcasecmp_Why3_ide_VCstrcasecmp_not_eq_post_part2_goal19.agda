-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19:
-- the strcasecmp mismatch verification condition, concluding that the
-- uppercased bytes cannot agree at every preceding offset under the stated
-- string-length, memory, address-order, separation, integer-range, linkedness,
-- constancy, and case-conversion assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module strcasecmp_Why3_ide_VCstrcasecmp_not_eq_post_part2_goal19 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

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

zeroZ oneZ thirtyTwoZ sixtyFiveZ ninetyZ ninetySevenZ
  oneHundredTwentyTwoZ oneHundredTwentyEightZ twoHundredFiftyFiveZ
  twoHundredFiftySixZ signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
thirtyTwoZ = pos 32
sixtyFiveZ = pos 65
ninetyZ = pos 90
ninetySevenZ = pos 97
oneHundredTwentyTwoZ = pos 122
oneHundredTwentyEightZ = pos 128
twoHundredFiftyFiveZ = pos 255
twoHundredFiftySixZ = pos 256
signed32Upper = pos 2147483648

signedByteLower signed32Lower : Int
signedByteLower = negsuc 127
signed32Lower = negsuc 2147483647

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

AddrLE : Addr → Addr → Set
AddrLE p q = offset p ≤Z offset q

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  Either
    (a ≤Z zeroZ)
    (Either
      (b ≤Z zeroZ)
      (Either
        (base p ≠ base q)
        (Either
          (addInt (offset q) b ≤Z offset p)
          (addInt (offset p) a ≤Z offset q))))

IsUint8 : Int → Set
IsUint8 x =
  (zeroZ ≤Z x) ∧
  (x <Z twoHundredFiftySixZ)

IsSint8 : Int → Set
IsSint8 x =
  (signedByteLower ≤Z x) ∧
  (x <Z oneHundredTwentyEightZ)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

IsLower : Int → Set
IsLower c =
  (ninetySevenZ ≤Z c) ∧
  (c ≤Z oneHundredTwentyTwoZ)

IsUpper : Int → Set
IsUpper c =
  (sixtyFiveZ ≤Z c) ∧
  (c ≤Z ninetyZ)

StringLengthProperty :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Set
StringLengthProperty allocation scalarMemory string length =
  scalarMemory (shift string length) ≡ zeroZ ∧
  zeroZ ≤Z length ∧
  ValidRW allocation (shift string zeroZ) (addInt oneZ length) ∧
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z length →
    scalarMemory (shift string index) ≠ zeroZ)

record StringLengthModel : Set where
  field
    stringLength : (Addr → Int) → Addr → Int
    stringLength-correct :
      (allocation : Int → Int) →
      (scalarMemory : Addr → Int) →
      (string : Addr) →
      (length : Int) →
      StringLengthProperty allocation scalarMemory string length →
      stringLength scalarMemory string ≡ length

open StringLengthModel

record Uint8Projection : Set where
  field
    toUint8 : Int → Int
    toUint8-in-range :
      (x : Int) →
      IsUint8 (toUint8 x)
    toUint8-identity :
      (x : Int) →
      IsUint8 x →
      toUint8 x ≡ x

open Uint8Projection

record ToUpperModel : Set where
  field
    toUpper : Int → Int
    toUpper-in-sint8 :
      (c : Int) →
      IsUint8 c →
      IsSint8 (toUpper c)
    toUpper-character :
      (c : Int) →
      IsUint8 c →
      IsLower c →
      addInt thirtyTwoZ (toUpper c) ≡ c ∧
      ((upperCharacter : Int) →
        IsUint8 upperCharacter →
        IsUpper upperCharacter →
        toUpper upperCharacter ≡ upperCharacter ∧
        ((otherCharacter : Int) →
          IsUint8 otherCharacter →
          Not (IsLower otherCharacter) →
          Not (IsUpper otherCharacter) →
          toUpper otherCharacter ≡ otherCharacter))

open ToUpperModel

Goal19 :
  StringLengthModel →
  Uint8Projection →
  ToUpperModel →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal19 lengthModel projection upperModel region linked sconst =
  (a a₁ a₂ : Addr) →
  (scalarMemory : Addr → Int) →
  (i₅ i₆ : Int) →
  (allocation : Int → Int) →
  (i i₁ i₄ i₂ i₃ : Int) →
  let
    x = base a
    x₁ = offset a₁
    x₂ = offset a
    a₃ = shift a₂ (subtractInt x₁ x₂)
    x₃ = scalarMemory a₁
    x₄ = stringLength lengthModel scalarMemory a
    x₅ = stringLength lengthModel scalarMemory a₂
    x₆ = toUint8 projection x₃
  in
  base a₁ ≡ x →
  Not
    (toUpper upperModel
      (toUint8 projection (scalarMemory (shift a₂ i₅)))
    ≡ toUpper upperModel
      (toUint8 projection (scalarMemory (shift a i₅)))) →
  scalarMemory a₃ ≡ zeroZ →
  zeroZ ≤Z i₅ →
  i₅ ≤Z i₆ →
  zeroZ ≤Z x₃ →
  region x ≤Z zeroZ →
  region (base a₂) ≤Z zeroZ →
  x₃ ≤Z twoHundredFiftyFiveZ →
  linked allocation →
  sconst scalarMemory →
  IsSint32 i →
  AddrLE a a₁ →
  IsSint8 x₃ →
  StringLengthProperty allocation scalarMemory a i₁ →
  StringLengthProperty allocation scalarMemory a i₄ →
  StringLengthProperty allocation scalarMemory a i₆ →
  StringLengthProperty allocation scalarMemory a₂ i₂ →
  StringLengthProperty allocation scalarMemory a₂ i₃ →
  StringLengthProperty allocation scalarMemory a₂ i₆ →
  AddrLE a₁ (shift a x₄) →
  Separated
    (shift a₂ zeroZ)
    (addInt oneZ x₅)
    (shift a zeroZ)
    (addInt oneZ x₄) →
  AddrLE a₂ a₃ →
  AddrLE a₃ (shift a₂ x₅) →
  (IsLower zeroZ → i ≡ negateInt thirtyTwoZ) →
  (IsUpper zeroZ → i ≡ zeroZ) →
  (Not (IsLower zeroZ) → Not (IsUpper zeroZ) → i ≡ zeroZ) →
  (IsUpper x₆ → x₃ ≡ i) →
  (IsLower x₆ → x₃ ≡ addInt thirtyTwoZ i) →
  (Not (IsLower x₆) → Not (IsUpper x₆) → x₃ ≡ i) →
  Not
    ((i₇ : Int) →
      zeroZ ≤Z i₇ →
      addInt i₇ x₂ <Z x₁ →
      toUpper upperModel
        (toUint8 projection (scalarMemory (shift a₂ i₇)))
      ≡ toUpper upperModel
        (toUint8 projection (scalarMemory (shift a i₇))))

strcasecmp-not-eq-post-part2-goal19 : Set₁
strcasecmp-not-eq-post-part2-goal19 =
  (lengthModel : StringLengthModel) →
  (projection : Uint8Projection) →
  (upperModel : ToUpperModel) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal19 lengthModel projection upperModel region linked sconst
