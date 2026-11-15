-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/__tolower_Why3_ide_VC__tolower_post_goal0:
-- under the unsigned-byte, signed-byte conversion, uppercase classification,
-- and C tolower assumptions, the returned byte equals the lowercase
-- conversion of the input byte. This file contains no proof.

{-# OPTIONS --safe #-}

module TolowerWhy3IdeVCTolowerPostGoal0 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_ _↔_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

zeroZ thirtyTwoZ sixtyFiveZ ninetyZ oneHundredTwentyEightZ
  twoHundredFiftySixZ : Int
zeroZ = pos zero
thirtyTwoZ = pos 32
sixtyFiveZ = pos 65
ninetyZ = pos 90
oneHundredTwentyEightZ = pos 128
twoHundredFiftySixZ = pos 256

signedByteLower : Int
signedByteLower = negsuc 127

IsUint8 : Int → Set
IsUint8 x =
  (zeroZ ≤Z x) ∧
  (x <Z twoHundredFiftySixZ)

IsSint8 : Int → Set
IsSint8 x =
  (signedByteLower ≤Z x) ∧
  (x <Z oneHundredTwentyEightZ)

IsUpper : Int → Set
IsUpper c =
  (sixtyFiveZ ≤Z c) ∧
  (c ≤Z ninetyZ)

record ByteConversion : Set where
  field
    toUint8 : Int → Int
    toSint8 : Int → Int

    toUint8-in-range :
      (x : Int) →
      IsUint8 (toUint8 x)

    toSint8-in-range :
      (x : Int) →
      IsSint8 (toSint8 x)

    toUint8-identity :
      (x : Int) →
      IsUint8 x →
      toUint8 x ≡ x

    toSint8-identity :
      (x : Int) →
      IsSint8 x →
      toSint8 x ≡ x

    toUint8-idempotent :
      (x : Int) →
      toUint8 (toUint8 x) ≡ toUint8 x

    toSint8-idempotent :
      (x : Int) →
      toSint8 (toSint8 x) ≡ toSint8 x

    signed-after-unsigned :
      (x : Int) →
      toSint8 (toUint8 x) ≡ toSint8 x

open ByteConversion

record ToLowerModel : Set where
  field
    toLower : Int → Int

    lower-A : toLower (pos 65) ≡ pos 97
    lower-B : toLower (pos 66) ≡ pos 98
    lower-C : toLower (pos 67) ≡ pos 99
    lower-D : toLower (pos 68) ≡ pos 100
    lower-E : toLower (pos 69) ≡ pos 101
    lower-F : toLower (pos 70) ≡ pos 102
    lower-G : toLower (pos 71) ≡ pos 103
    lower-H : toLower (pos 72) ≡ pos 104
    lower-I : toLower (pos 73) ≡ pos 105
    lower-J : toLower (pos 74) ≡ pos 106
    lower-K : toLower (pos 75) ≡ pos 107
    lower-L : toLower (pos 76) ≡ pos 108
    lower-M : toLower (pos 77) ≡ pos 109
    lower-N : toLower (pos 78) ≡ pos 110
    lower-O : toLower (pos 79) ≡ pos 111
    lower-P : toLower (pos 80) ≡ pos 112
    lower-Q : toLower (pos 81) ≡ pos 113
    lower-R : toLower (pos 82) ≡ pos 114
    lower-S : toLower (pos 83) ≡ pos 115
    lower-T : toLower (pos 84) ≡ pos 116
    lower-U : toLower (pos 85) ≡ pos 117
    lower-V : toLower (pos 86) ≡ pos 118
    lower-W : toLower (pos 87) ≡ pos 119
    lower-X : toLower (pos 88) ≡ pos 120
    lower-Y : toLower (pos 89) ≡ pos 121
    lower-Z : toLower (pos 90) ≡ pos 122

    lower-non-uppercase :
      (c : Int) →
      Not (IsUpper c) →
      toLower c ≡ c

open ToLowerModel

Goal0 :
  ByteConversion →
  ToLowerModel →
  Set
Goal0 conversion lowerModel =
  (i₁ i i₂ : Int) →
  (IsUpper (toSint8 conversion i₁) ↔ Not (i ≡ zeroZ)) →
  IsUint8 i →
  IsUint8 i₁ →
  IsUint8 i₂ →
  IfSet
    (intEqual i zeroZ)
    (i₂ ≡ i₁)
    (toUint8 conversion (addInt thirtyTwoZ i₁) ≡ i₂) →
  toLower lowerModel i₁ ≡ i₂

tolower-post-goal0 : Set
tolower-post-goal0 =
  (conversion : ByteConversion) →
  (lowerModel : ToLowerModel) →
  Goal0 conversion lowerModel
