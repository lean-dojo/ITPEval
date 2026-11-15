-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strpbrk_Why3_ide_VCstrpbrk_assert_4_goal16:
-- under the stated C memory, string-validity, address-order, integer-range,
-- linkedness, constancy, string-search, and prior-byte assumptions, the bytes
-- at the two designated addresses are distinct. This file contains no proof.

{-# OPTIONS --safe #-}

module StrpbrkWhy3IdeVCstrpbrkAssert4Goal16 where

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

zeroAddr : Addr
zeroAddr = addr zeroZ zeroZ

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

record AddressOrder : Set₁ where
  field
    addrLE : Addr → Addr → Set
    addrLT : Addr → Addr → Set

    addrLE-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLE p q) (offset p ≤Z offset q)

    addrLT-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLT p q) (offset p <Z offset q)

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

record IntegerConversion : Set where
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

open IntegerConversion

record StringOperations
  (conversion : IntegerConversion)
  (order : AddressOrder) : Set₁ where
  field
    lStrlen : (Addr → Int) → Addr → Int
    lStrpbrk : Addr → Addr → Addr

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

    lStrpbrk-base-case :
      (scalar-memory : Addr → Int) →
      (string accept : Addr) →
      scalar-memory string ≡ zeroZ →
      lStrpbrk string accept ≡ zeroAddr

    lStrpbrk-found :
      (scalar-memory : Addr → Int) →
      (string accept : Addr) →
      scalar-memory string ≠ zeroZ →
      Exists Addr
        (λ member →
          (scalar-memory member ≡ scalar-memory string) ∧
          addrLE order accept member ∧
          addrLT order member
            (shift accept (lStrlen scalar-memory accept))) →
      lStrpbrk string accept ≡ string

    lStrpbrk-not-found :
      (scalar-memory : Addr → Int) →
      (string accept : Addr) →
      scalar-memory string ≠ zeroZ →
      Not
        (Exists Addr
          (λ member →
            (scalar-memory member ≡ scalar-memory string) ∧
            addrLE order accept member ∧
            addrLT order member
              (shift accept (lStrlen scalar-memory accept)))) →
      lStrpbrk (shift string oneZ) accept ≡ lStrpbrk string accept

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

PInArray :
  {conversion : IntegerConversion} →
  {order : AddressOrder} →
  StringOperations conversion order →
  (Addr → Int) →
  Addr →
  Int →
  Set
PInArray {order = order} string-model scalar-memory string character =
  Exists Addr
    (λ member →
      (scalar-memory member ≡ character) ∧
      addrLE order string member ∧
      addrLT order member
        (shift string (lStrlen string-model scalar-memory string)))

Goal16 :
  (conversion : IntegerConversion) →
  (order : AddressOrder) →
  StringOperations conversion order →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal16 conversion order string-model region linked sconst =
  (scalar-memory : Addr → Int) →
  (a₁ a₂ a a₃ : Addr) →
  (allocation : Int → Int) →
  (a₄ a₅ : Addr) →
  let
    x = scalar-memory a₁
    a₆ = shift a₂ (lStrlen string-model scalar-memory a₂)
  in
  scalar-memory a ≡ zeroZ →
  x ≠ zeroZ →
  lStrpbrk string-model a₃ a₂ ≡ lStrpbrk string-model a₁ a₂ →
  region (base a₂) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  linked allocation →
  sconst scalar-memory →
  addrLE order a₂ a →
  addrLE order a₂ a₄ →
  addrLE order a₃ a₁ →
  addrLE order a₃ a₅ →
  addrLE order a₅ a₁ →
  IsSint8 x →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₁ →
  PValidString allocation scalar-memory a₂ →
  PValidString allocation scalar-memory a₃ →
  addrLT order a₄ a₆ →
  addrLE order a a₆ →
  addrLE order a₁
    (shift a₃ (lStrlen string-model scalar-memory a₃)) →
  (PInArray string-model scalar-memory a₂ x →
    PInArray string-model scalar-memory a x) →
  ((a₇ : Addr) →
    addrLT order a₇ a →
    addrLE order a₂ a₇ →
    x ≠ scalar-memory a₇) →
  ((a₇ : Addr) →
    addrLE order a₂ a₇ →
    addrLT order a₇ a₆ →
    x ≠ scalar-memory a₇) →
  ((a₈ a₇ : Addr) →
    addrLT order a₈ a₁ →
    addrLE order a₂ a₇ →
    addrLE order a₃ a₈ →
    addrLT order a₇ a₆ →
    scalar-memory a₈ ≠ scalar-memory a₇) →
  scalar-memory a₅ ≠ scalar-memory a₄

strpbrk-assert-4-goal16 : Set₁
strpbrk-assert-4-goal16 =
  (conversion : IntegerConversion) →
  (order : AddressOrder) →
  (string-model : StringOperations conversion order) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal16 conversion order string-model region linked sconst
