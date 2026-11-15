-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strncmp_Why3_ide_VCstrncmp_len_diff_post_2_goal23:
-- under the stated C integer-range, address-order, memory-validity,
-- linkedness, constancy, bounded-string, string-length, byte-conversion,
-- offset, and equal-prefix assumptions, the comparison result is one.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module StrncmpWhy3IdeVCstrncmpLenDiffPost2Goal23 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

boolOr : Bool → Bool → Bool
boolOr true _ = true
boolOr false value = value

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

zeroZ oneZ minusOneZ signed8Lower signed8Upper signed32Lower
  signed32Upper uint8Upper uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero
signed8Lower = negsuc 127
signed8Upper = pos 128
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint8Upper = pos 256
uint64Upper = pos 18446744073709551616

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

record AddressOrder : Set₁ where
  field
    addrLE     : Addr → Addr → Set
    addrLEBool : Addr → Addr → Bool

    addrLE-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLE p q) (offset p ≤Z offset q)

    addrLE-boolean-characterization :
      (p q : Addr) →
      Iff (addrLE p q) (addrLEBool p q ≡ true)

open AddressOrder

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsSint8 : Int → Set
IsSint8 x =
  (signed8Lower ≤Z x) ∧
  (x <Z signed8Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

IsUint8 : Int → Set
IsUint8 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint8Upper)

IsUint64 : Int → Set
IsUint64 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint64Upper)

record IntegerConversion : Set where
  field
    toUint8  : Int → Int
    toUint64 : Int → Int

    toUint8-in-range :
      (x : Int) →
      IsUint8 (toUint8 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toUint8-identity :
      (x : Int) →
      IsUint8 x →
      toUint8 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toUint8-idempotent :
      (x : Int) →
      toUint8 (toUint8 x) ≡ toUint8 x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

open IntegerConversion

record StringOperations (conversion : IntegerConversion) : Set where
  field
    lStrlen  : (Addr → Int) → Addr → Int
    lStrnlen : (Addr → Int) → Addr → Int → Int

    lStrlen-fix :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      IfSet
        (intEqual (scalar-memory (shift string zeroZ)) zeroZ)
        (lStrlen scalar-memory string ≡ zeroZ)
        (toUint64 conversion
          (addInt oneZ (lStrlen scalar-memory (shift string oneZ)))
          ≡ lStrlen scalar-memory string)

    lStrlen-in-range :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      IsUint64 (lStrlen scalar-memory string)

    lStrnlen-fix :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      (count : Int) →
      IfSet
        (boolOr
          (intEqual count zeroZ)
          (intEqual (scalar-memory (shift string zeroZ)) zeroZ))
        (lStrnlen scalar-memory string count ≡ zeroZ)
        (toUint64 conversion
          (addInt oneZ
            (lStrnlen
              scalar-memory
              (shift string oneZ)
              (toUint64 conversion (subtractInt count oneZ))))
          ≡ lStrnlen scalar-memory string count)

    lStrnlen-in-range :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      (count : Int) →
      IsUint64 (lStrnlen scalar-memory string count)

open StringOperations

PValidString :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Set
PValidString allocation scalar-memory string =
  Exists Int
    (λ terminator →
      (scalar-memory (shift string terminator) ≡ zeroZ) ∧
      IsUint64 terminator ∧
      ValidRW
        allocation
        (shift string zeroZ)
        (addInt oneZ terminator) ∧
      ((index : Int) →
        index ≤Z terminator →
        IsSint8 (scalar-memory (shift string index))))

PValidStringN :
  (Int → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Set
PValidStringN allocation scalar-memory string count =
  let start = shift string zeroZ
  in
  ValidRW allocation start (addInt oneZ count) ∨
  (Exists Int
    (λ terminator →
      (scalar-memory (shift string terminator) ≡ zeroZ) ∧
      (terminator <Z count) ∧
      IsUint64 terminator ∧
      ValidRW allocation start (addInt oneZ terminator)) ∧
  ((index : Int) →
    index ≤Z count →
    IsSint8 (scalar-memory (shift string index))))

Goal23 :
  AddressOrder →
  (conversion : IntegerConversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal23 address-order conversion string-model region linked sconst =
  (a₁ a₂ a a₃ : Addr) →
  (i₁ : Int) →
  (scalar-memory : Addr → Int) →
  (allocation : Int → Int) →
  (i₂ i₃ i : Int) →
  let
    x = offset a₁
    x₁ = offset a₂
    x₂ = offset a
    x₃ = offset a₃
    x₄ = subtractInt (addInt i₁ x) x₂
    x₅ = lStrnlen string-model scalar-memory a₁ i₁
    x₆ = addInt x x₅
    x₇ = lStrnlen string-model scalar-memory a₃ i₁
    x₈ = addInt i₁ x
  in
  addInt x x₁ ≡ addInt x₂ x₃ →
  addInt x₂ (lStrnlen string-model scalar-memory a x₄) ≡ x₆ →
  addInt x₁ (lStrnlen string-model scalar-memory a₂ x₄)
    ≡ addInt x₃ x₇ →
  zeroZ <Z i₁ →
  x ≤Z x₂ →
  region (base a₁) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  x₅ <Z x₇ →
  x₂ ≤Z x₈ →
  linked allocation →
  sconst scalar-memory →
  IsUint8 i₂ →
  IsUint8 i₃ →
  IsSint32 i →
  IsUint64 i₁ →
  addrLE address-order a₁ a →
  addrLE address-order a₃ a₂ →
  PValidStringN allocation scalar-memory a₁ i₁ →
  PValidStringN allocation scalar-memory a₃ i₁ →
  IsUint64 x₄ →
  addrLE address-order a (shift a₁ x₅) →
  addrLE address-order a₂ (shift a₃ x₇) →
  PValidStringN allocation scalar-memory a x₄ →
  PValidStringN allocation scalar-memory a₂ x₄ →
  IfSet
    (intEqual x₈ x₂)
    (i ≡ zeroZ)
    ((toUint8 conversion (scalar-memory a) ≡ i₂) ∧
     (toUint8 conversion (scalar-memory a₂) ≡ i₃) ∧
     IfSet
       (intEqual i₃ i₂)
       ((i ≡ zeroZ) ∧ (i₃ ≡ zeroZ))
       (IfSet
         (intLess i₃ i₂)
         (i ≡ minusOneZ)
         (i ≡ oneZ)) ∧
     ((i₂ ≡ zeroZ) →
       (x₅ ≡ lStrlen string-model scalar-memory a₁) ∧
       (x₆ ≡ x₂) ∧
       PValidString allocation scalar-memory a₁) ∧
     ((i₃ ≡ zeroZ) →
       (x₇ ≡ lStrlen string-model scalar-memory a₃) ∧
       (addInt x x₇ ≡ x₂) ∧
       PValidString allocation scalar-memory a₃)) →
  ((i₄ : Int) →
    zeroZ ≤Z i₄ →
    i₄ <Z x₇ →
    scalar-memory (shift a₃ i₄) ≡ scalar-memory (shift a₁ i₄)) →
  ((i₄ : Int) →
    zeroZ ≤Z i₄ →
    addInt i₄ x <Z x₂ →
    scalar-memory (shift a₃ i₄) ≡ scalar-memory (shift a₁ i₄)) →
  ((i₄ : Int) →
    let
      x₉ = scalar-memory (shift a₃ i₄)
      x₁₀ = scalar-memory (shift a₁ i₄)
    in
    zeroZ ≤Z i₄ →
    i₄ <Z x₇ →
    Iff
      (toUint8 conversion x₉ ≡ toUint8 conversion x₁₀)
      (x₉ ≡ x₁₀)) →
  i ≡ oneZ

strncmp-length-difference-post-2-goal23 : Set₁
strncmp-length-difference-post-2-goal23 =
  (address-order : AddressOrder) →
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal23
    address-order
    conversion
    string-model
    region
    linked
    sconst
