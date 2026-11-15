-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strnlen_Why3_ide_VCstrnlen_loop_inv_6_preserved_goal8:
-- under the stated nonzero-count and nonzero-byte, offset, address-order,
-- integer-range, memory-validity, linkedness, constancy, bounded-string, and
-- preceding-byte assumptions, the byte at the current shifted index is
-- nonzero. This file contains no proof.

{-# OPTIONS --safe #-}

module StrnlenWhy3IdeVCstrnlenLoopInv6PreservedGoal8 where

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

zeroZ oneZ signed8Lower signed8Upper uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signed8Lower = negsuc 127
signed8Upper = pos 128
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

IsUint64 : Int → Set
IsUint64 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint64Upper)

record Uint64Conversion : Set where
  field
    toUint64 : Int → Int

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

open Uint64Conversion

record StringOperations (conversion : Uint64Conversion) : Set where
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

Goal8 :
  (conversion : Uint64Conversion) →
  StringOperations conversion →
  AddressOrder →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal8 conversion string-model address-order region linked sconst =
  (scalar-memory : Addr → Int) →
  (a a₁ : Addr) →
  (count index : Int) →
  (allocation : Int → Int) →
  let
    current-byte = scalar-memory a
    initial-offset = offset a₁
    current-offset = offset a
    remaining-count =
      subtractInt (addInt count current-offset) initial-offset
    suffix-length =
      lStrnlen string-model scalar-memory a₁ remaining-count
  in
  count ≠ zeroZ →
  current-byte ≠ zeroZ →
  addInt initial-offset suffix-length ≡
    addInt current-offset
      (lStrnlen string-model scalar-memory a count) →
  zeroZ ≤Z index →
  zeroZ ≤Z count →
  initial-offset ≤Z current-offset →
  region (base a₁) ≤Z zeroZ →
  addInt index initial-offset ≤Z current-offset →
  linked allocation →
  sconst scalar-memory →
  IsUint64 count →
  addrLE address-order a₁ a →
  IsSint8 current-byte →
  PValidStringN allocation scalar-memory a count →
  IsUint64 remaining-count →
  PValidStringN
    allocation
    scalar-memory
    a₁
    remaining-count →
  addrLE address-order a (shift a₁ suffix-length) →
  ((prior-index : Int) →
    zeroZ ≤Z prior-index →
    addInt prior-index initial-offset <Z current-offset →
    scalar-memory (shift a₁ prior-index) ≠ zeroZ) →
  scalar-memory (shift a₁ index) ≠ zeroZ

strnlen-loop-invariant-6-preserved-goal8 : Set₁
strnlen-loop-invariant-6-preserved-goal8 =
  (conversion : Uint64Conversion) →
  (string-model : StringOperations conversion) →
  (address-order : AddressOrder) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal8
    conversion
    string-model
    address-order
    region
    linked
    sconst
