-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strspn_Why3_ide_VCstrspn_post_3_goal1:
-- under the stated C memory, string-validity, address-order, integer-range,
-- linkedness, constancy, string-span, conditional exit-state, and prior-byte
-- assumptions, the byte at the designated source address occurs within the
-- accept string. This file contains no proof.

{-# OPTIONS --safe #-}

module StrspnWhy3IdeVCstrspnPost3Goal1 where

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
    lStrspn : Addr → Addr → Int

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

    lStrspn-base-case :
      (scalar-memory : Addr → Int) →
      (string accept : Addr) →
      scalar-memory string ≡ zeroZ →
      lStrspn string accept ≡ zeroZ

    lStrspn-not-in-accept :
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
      lStrspn string accept ≡ zeroZ

    lStrspn-in-accept :
      (scalar-memory : Addr → Int) →
      (string accept : Addr) →
      scalar-memory string ≠ zeroZ →
      Exists Addr
        (λ member →
          (scalar-memory member ≡ scalar-memory string) ∧
          addrLE order accept member ∧
          addrLT order member
            (shift accept (lStrlen scalar-memory accept))) →
      addInt oneZ (lStrspn (shift string oneZ) accept)
        ≡ lStrspn string accept

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

Goal1 :
  (conversion : IntegerConversion) →
  (order : AddressOrder) →
  StringOperations conversion order →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal1 conversion order string-model region linked sconst =
  (a₁ a : Addr) →
  (scalar-memory : Addr → Int) →
  (a₂ a₃ : Addr) →
  (allocation : Int → Int) →
  (i : Int) →
  (a₅ : Addr) →
  (i₁ i₂ : Int) →
  (a₄ : Addr) →
  let
    x = offset a₁
    x₁ = offset a
    x₂ = lStrlen string-model scalar-memory a
    x₃ = scalar-memory a₁
    x₄ = scalar-memory a₂
    a₆ = shift a₃ (lStrlen string-model scalar-memory a₃)
  in
  addInt x (lStrspn string-model a₁ a₃)
    ≡ addInt x₁ (lStrspn string-model a a₃) →
  x₁ ≤Z x →
  region (base a) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  x ≤Z addInt x₁ x₂ →
  linked allocation →
  sconst scalar-memory →
  IsUint64 i →
  addrLE order a a₁ →
  addrLE order a a₅ →
  IsSint8 x₃ →
  IsSint8 x₄ →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₁ →
  PValidString allocation scalar-memory a₃ →
  addrLT order a₅ (shift a i) →
  IsUint64 (subtractInt x x₁) →
  addrLE order a₁ (shift a x₂) →
  IfSet
    (intEqual x₃ zeroZ)
    ((i₁ ≡ i) ∧
      (addInt i₁ x₁ ≡ x))
    ((a₂ ≡ a₁) ∧
      (i₂ ≡ i) ∧
      (scalar-memory a₄ ≡ zeroZ) ∧
      (addInt i₂ x₁ ≡ offset a₂) ∧
      addrLE order a₃ a₄ ∧
      PValidString allocation scalar-memory a₄ ∧
      Not (PInArray string-model scalar-memory a₃ x₄) ∧
      addrLE order a₄ a₆ ∧
      ((a₇ : Addr) →
        addrLT order a₇ a₄ →
        addrLE order a₃ a₇ →
        x₄ ≠ scalar-memory a₇)) →
  ((a₇ : Addr) →
    addrLT order a₇ a₁ →
    addrLE order a a₇ →
    Exists Addr
      (λ a₈ →
        (scalar-memory a₇ ≡ scalar-memory a₈) ∧
        addrLE order a₃ a₈ ∧
        addrLT order a₈ a₆)) →
  Exists Addr
    (λ a₇ →
      (scalar-memory a₅ ≡ scalar-memory a₇) ∧
      addrLE order a₃ a₇ ∧
      addrLT order a₇ a₆)

strspn-post-3-goal1 : Set₁
strspn-post-3-goal1 =
  (conversion : IntegerConversion) →
  (order : AddressOrder) →
  (string-model : StringOperations conversion order) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal1 conversion order string-model region linked sconst
