-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strncmp_Why3_ide_VCstrncmp_loop_inv_6_preserved_goal12:
-- under the stated byte-conversion, address-offset, bounded-string,
-- memory-validity, address-order, integer-range, linkedness, constancy, and
-- equal-prefix assumptions, the common offset-plus-bounded-length endpoint
-- equals one plus the second offset and the bounded length after advancing
-- that address and decrementing the count. This file contains no proof.

{-# OPTIONS --safe #-}

module StrncmpWhy3IdeVCstrncmpLoopInv6PreservedGoal12 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

negateInt : Int → Int
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

zeroZ oneZ signed8Lower signed8Upper signed64Lower signed64Upper
  uint8Upper uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signed8Lower = negsuc 127
signed8Upper = pos 128
signed64Lower = negsuc 9223372036854775807
signed64Upper = pos 9223372036854775808
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

    addrLE-bool-characterization :
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

IsSint64 : Int → Set
IsSint64 x =
  (signed64Lower ≤Z x) ∧
  (x <Z signed64Upper)

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
    toSint8  : Int → Int
    toUint64 : Int → Int
    toSint64 : Int → Int

    toUint8-in-range :
      (x : Int) →
      IsUint8 (toUint8 x)

    toSint8-in-range :
      (x : Int) →
      IsSint8 (toSint8 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toSint64-in-range :
      (x : Int) →
      IsSint64 (toSint64 x)

    toUint8-identity :
      (x : Int) →
      IsUint8 x →
      toUint8 x ≡ x

    toSint8-identity :
      (x : Int) →
      IsSint8 x →
      toSint8 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toSint64-identity :
      (x : Int) →
      IsSint64 x →
      toSint64 x ≡ x

    toUint8-idempotent :
      (x : Int) →
      toUint8 (toUint8 x) ≡ toUint8 x

    toSint8-idempotent :
      (x : Int) →
      toSint8 (toSint8 x) ≡ toSint8 x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

    toSint64-idempotent :
      (x : Int) →
      toSint64 (toSint64 x) ≡ toSint64 x

    proj-int8 :
      (x : Int) →
      toSint8 (toUint8 x) ≡ toSint8 x

    proj-int64 :
      (x : Int) →
      toSint64 (toUint64 x) ≡ toSint64 x

open IntegerConversion

record StringOperations (conversion : IntegerConversion) : Set where
  field
    lStrnlen : (Addr → Int) → Addr → Int → Int

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

Goal12 :
  (conversion : IntegerConversion) →
  StringOperations conversion →
  AddressOrder →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal12 conversion string-model address-order region linked sconst =
  (scalar-memory : Addr → Int) →
  (a₂ a₃ a₁ a : Addr) →
  (i : Int) →
  (allocation : Int → Int) →
  let
    x = scalar-memory a₂
    x₁ = toUint8 conversion x
    x₂ = scalar-memory a₃
    x₃ = offset a₁
    x₄ = offset a₃
    x₅ = offset a
    x₆ = offset a₂
    x₇ = subtractInt x₄ x₅
    x₈ = scalar-memory (shift a₁ x₇)
    x₉ = scalar-memory (shift a x₇)
    x₁₀ = subtractInt (addInt i x₆) x₃
    x₁₁ = lStrnlen string-model scalar-memory a x₁₀
    x₁₂ = addInt x₅ x₁₁
    x₁₃ = lStrnlen string-model scalar-memory a₁ x₁₀
  in
  i ≠ zeroZ →
  x₁ ≠ zeroZ →
  toUint8 conversion x₂ ≡ x₁ →
  addInt x₃ x₄ ≡ addInt x₅ x₆ →
  x₈ ≡ x₉ →
  x₁₂
    ≡ addInt x₄ (lStrnlen string-model scalar-memory a₃ i) →
  addInt x₃ x₁₃
    ≡ addInt x₆ (lStrnlen string-model scalar-memory a₂ i) →
  zeroZ ≤Z i →
  x₃ ≤Z x₆ →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  sconst scalar-memory →
  IsUint64 i →
  addrLE address-order a a₃ →
  addrLE address-order a₁ a₂ →
  IsSint8 x →
  IsSint8 x₂ →
  PValidStringN allocation scalar-memory a₂ i →
  PValidStringN allocation scalar-memory a₃ i →
  IsUint64 x₁₀ →
  IsSint8 x₉ →
  IsSint8 x₈ →
  PValidStringN allocation scalar-memory a x₁₀ →
  PValidStringN allocation scalar-memory a₁ x₁₀ →
  addrLE address-order a₂ (shift a₁ x₁₃) →
  addrLE address-order a₃ (shift a x₁₁) →
  ((i₁ : Int) →
    zeroZ ≤Z i₁ →
    addInt i₁ x₃ <Z x₆ →
    scalar-memory (shift a₁ i₁) ≡ scalar-memory (shift a i₁)) →
  ((i₁ : Int) →
    let
      x₁₄ = scalar-memory (shift a₁ i₁)
      x₁₅ = scalar-memory (shift a i₁)
    in
    zeroZ ≤Z i₁ →
    i₁ <Z x₁₁ →
    Iff
      (toUint8 conversion x₁₄ ≡ toUint8 conversion x₁₅)
      (x₁₄ ≡ x₁₅)) →
  x₁₂
    ≡ addInt
        (addInt oneZ x₄)
        (lStrnlen
          string-model
          scalar-memory
          (shift a₃ oneZ)
          (toUint64 conversion (subtractInt i oneZ)))

strncmp-loop-invariant-6-preserved-goal12 : Set₁
strncmp-loop-invariant-6-preserved-goal12 =
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (address-order : AddressOrder) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal12
    conversion
    string-model
    address-order
    region
    linked
    sconst
