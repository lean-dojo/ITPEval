-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strncpy_Why3_ide_VCstrncpy_not_exceed_post_2_goal19:
-- under the stated address, memory, C integer-range, string-validity,
-- bounded-string, linkedness, constancy, havoc, and equal-prefix assumptions,
-- the destination is a valid bounded string. This file contains no proof.

{-# OPTIONS --safe #-}

module StrncpyWhy3IdeVCstrncpyNotExceedPost2Goal19 where

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

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true when-false = when-true
ifValue false when-true when-false = when-false

boolOr : Bool → Bool → Bool
boolOr true _ = true
boolOr false value = value

notBool : Bool → Bool
notBool true = false
notBool false = true

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

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

    addrLE-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLE p q) (offset p ≤Z offset q)

open AddressOrder

separatedBool : Addr → Int → Addr → Int → Bool
separatedBool p a q b =
  boolOr
    (intLessOrEqual a zeroZ)
    (boolOr
      (intLessOrEqual b zeroZ)
      (boolOr
        (notBool (intEqual (base p) (base q)))
        (boolOr
          (intLessOrEqual (addInt (offset q) b) (offset p))
          (intLessOrEqual (addInt (offset p) a) (offset q)))))

havoc :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Int
havoc old-memory new-memory location size query =
  ifValue
    (separatedBool query oneZ location size)
    (new-memory query)
    (old-memory query)

PointwiseEqual : {A B : Set} → (A → B) → (A → B) → Set
PointwiseEqual {A = A} f g = (x : A) → f x ≡ g x

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

Goal19 :
  AddressOrder →
  (conversion : Uint64Conversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal19 address-order conversion string-model region linked sconst =
  (a₃ a₁ a : Addr) →
  (t₁ t₂ t₃ : Addr → Int) →
  (allocation : Int → Int) →
  (a₂ : Addr) →
  let
    x = base a₃
    x₁ = base a₁
    a₄ = shift a₁ zeroZ
    x₂ = offset a₁
    x₃ = offset a
    x₄ = subtractInt x₃ x₂
  in
  x ≠ x₁ →
  PointwiseEqual
    (havoc
      t₁
      t₂
      a₄
      (addInt oneZ (lStrnlen string-model t₃ a₃ zeroZ)))
    t₃ →
  x₂ ≤Z x₃ →
  region x₁ ≤Z zeroZ →
  region x ≤Z zeroZ →
  x₃ <Z addInt x₂ (lStrlen string-model t₂ a₃) →
  linked allocation →
  sconst t₂ →
  addrLE address-order a₁ a →
  addrLE address-order a₃ a₂ →
  PValidString allocation t₂ a₃ →
  PValidString allocation t₃ a₂ →
  IsUint64 x₄ →
  PValidStringN allocation t₂ a₃ x₄ →
  PValidStringN allocation t₃ a x₄ →
  addrLE address-order a (shift a₁ x₄) →
  addrLE
    address-order
    a₂
    (shift a₃ (lStrnlen string-model t₃ a₃ x₄)) →
  ValidRW
    allocation
    a₄
    (addInt oneZ (lStrnlen string-model t₂ a₃ x₄)) →
  ((index : Int) →
    zeroZ ≤Z index →
    addInt index (offset a₃) <Z offset a₂ →
    t₃ (shift a₃ index) ≡ t₃ (shift a₁ index)) →
  PValidStringN allocation t₃ a₁ x₄

strncpy-not-exceed-post-2-goal19 : Set₁
strncpy-not-exceed-post-2-goal19 =
  (address-order : AddressOrder) →
  (conversion : Uint64Conversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal19
    address-order
    conversion
    string-model
    region
    linked
    sconst
