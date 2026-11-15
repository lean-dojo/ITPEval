-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strchr_Why3_ide_VCstrchr_exists_post_3_goal12:
-- under the stated C memory, string-validity, address-order, integer-range,
-- linkedness, constancy, branch-characterization, and prior-byte assumptions,
-- the byte at the specified address differs from the searched signed byte.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module StrchrWhy3IdeVCstrchrExistsPost3Goal12 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infix 2 _↔_

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

record _↔_ (A B : Set) : Set where
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

zeroZ oneZ signed8Lower signed8Upper signed32Lower signed32Upper
  uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signed8Lower = negsuc 127
signed8Upper = pos 128
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
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
      (addrLE p q ↔ (offset p ≤Z offset q))

    addrLT-same-base :
      (p q : Addr) →
      base p ≡ base q →
      (addrLT p q ↔ (offset p <Z offset q))

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

IsUint64 : Int → Set
IsUint64 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint64Upper)

record IntegerConversion : Set where
  field
    toSint8  : Int → Int
    toUint64 : Int → Int

    toSint8-in-range :
      (x : Int) →
      IsSint8 (toSint8 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toSint8-identity :
      (x : Int) →
      IsSint8 x →
      toSint8 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toSint8-idempotent :
      (x : Int) →
      toSint8 (toSint8 x) ≡ toSint8 x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

open IntegerConversion

record StringOperations (conversion : IntegerConversion) : Set where
  field
    lStrlen : (Addr → Int) → Addr → Int
    lStrchr : (Addr → Int) → Addr → Int → Addr

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

    lStrchr-fix :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      (character : Int) →
      IfSet
        (intEqual (scalar-memory string) character)
        (lStrchr scalar-memory string character ≡ string)
        (IfSet
          (intEqual (scalar-memory string) zeroZ)
          (lStrchr scalar-memory string character ≡ zeroAddr)
          (lStrchr scalar-memory (shift string oneZ) character
            ≡ lStrchr scalar-memory string character))

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

Goal12 :
  AddressOrder →
  (conversion : IntegerConversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal12 order conversion string-model region linked sconst =
  (scalar-memory : Addr → Int) →
  (a₃ a a₁ a₂ : Addr) →
  (i : Int) →
  (allocation : Int → Int) →
  (a₄ : Addr) →
  let
    x = scalar-memory a₃
    x₁ = scalar-memory a
    x₂ = scalar-memory a₁
    a₅ = shift a₂ (lStrlen string-model scalar-memory a₂)
  in
  x ≡ toSint8 conversion i →
  lStrchr string-model scalar-memory a₂ x
    ≡ lStrchr string-model scalar-memory a x →
  region (base a₂) ≤Z zeroZ →
  linked allocation →
  sconst scalar-memory →
  IsSint32 i →
  addrLT order a₄ a₁ →
  addrLE order a₂ a →
  addrLE order a₂ a₃ →
  addrLE order a₂ a₄ →
  IsSint8 x₁ →
  IsSint8 x₂ →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₂ →
  addrLE order a a₅ →
  addrLE order a₃ a₅ →
  IfSet
    (intEqual x x₁)
    ((a₁ ≡ a) ∧
     ((a₅ ≡ a₁) ↔ (x₂ ≡ zeroZ)) ∧
     (addrLT order a₁ a₅ ↔ (x₂ ≠ zeroZ)))
    ((zeroAddr ≡ a₁) ∧ (x₁ ≡ zeroZ)) →
  ((a₆ : Addr) →
    addrLT order a₆ a →
    addrLE order a₂ a₆ →
    x ≠ scalar-memory a₆) →
  scalar-memory a₄ ≠ x

strchr-exists-post-3-goal12 : Set₁
strchr-exists-post-3-goal12 =
  (order : AddressOrder) →
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal12 order conversion string-model region linked sconst
