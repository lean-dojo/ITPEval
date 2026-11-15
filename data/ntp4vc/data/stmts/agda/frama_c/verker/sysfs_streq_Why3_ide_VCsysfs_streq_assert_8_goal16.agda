-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_assert_8_goal16:
-- under the stated C memory, string-validity, integer-range, linkedness,
-- constancy, equal-prefix, and nonzero-byte-prefix assumptions, the sysfs
-- string length of the first address is the given index. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module SysfsStreqWhy3IdeVCsysfsStreqAssert8Goal16 where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

boolAnd : Bool → Bool → Bool
boolAnd true value = value
boolAnd false _ = false

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

zeroZ oneZ tenZ signed8Lower signed8Upper uint32Upper signed32Lower
  signed32Upper uint64Upper signed64Lower signed64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
tenZ = pos 10
signed8Lower = negsuc 127
signed8Upper = pos 128
uint32Upper = pos 4294967296
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
uint64Upper = pos 18446744073709551616
signed64Lower = negsuc 9223372036854775807
signed64Upper = pos 9223372036854775808

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

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

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

IsUint64 : Int → Set
IsUint64 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint64Upper)

IsSint64 : Int → Set
IsSint64 x =
  (signed64Lower ≤Z x) ∧
  (x <Z signed64Upper)

record IntegerConversion : Set where
  field
    toUint32 : Int → Int
    toSint32 : Int → Int
    toUint64 : Int → Int
    toSint64 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toSint32-in-range :
      (x : Int) →
      IsSint32 (toSint32 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toSint64-in-range :
      (x : Int) →
      IsSint64 (toSint64 x)

    toUint32-identity :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

    toSint32-identity :
      (x : Int) →
      IsSint32 x →
      toSint32 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toSint64-identity :
      (x : Int) →
      IsSint64 x →
      toSint64 x ≡ x

    toUint32-idempotent :
      (x : Int) →
      toUint32 (toUint32 x) ≡ toUint32 x

    toSint32-idempotent :
      (x : Int) →
      toSint32 (toSint32 x) ≡ toSint32 x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

    toSint64-idempotent :
      (x : Int) →
      toSint64 (toSint64 x) ≡ toSint64 x

    proj-int32 :
      (x : Int) →
      toSint32 (toUint32 x) ≡ toSint32 x

    proj-int64 :
      (x : Int) →
      toSint64 (toUint64 x) ≡ toSint64 x

open IntegerConversion

record StringOperations (conversion : IntegerConversion) : Set where
  field
    lStrlen       : (Addr → Int) → Addr → Int
    lSysfsStrlen  : (Addr → Int) → Addr → Int
    lStrncmp      : (Addr → Int) → Addr → Addr → Int → Int

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

    lSysfsStrlen-fix :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      IfSet
        (boolOr
          (intEqual (scalar-memory (shift string zeroZ)) zeroZ)
          (boolAnd
            (intEqual (scalar-memory (shift string zeroZ)) tenZ)
            (intEqual (scalar-memory (shift string oneZ)) zeroZ)))
        (lSysfsStrlen scalar-memory string ≡ zeroZ)
        (toUint64 conversion
          (addInt oneZ
            (lSysfsStrlen scalar-memory (shift string oneZ)))
          ≡ lSysfsStrlen scalar-memory string)

    lSysfsStrlen-in-range :
      (scalar-memory : Addr → Int) →
      (string : Addr) →
      IsUint64 (lSysfsStrlen scalar-memory string)

    lStrncmp-fix :
      (scalar-memory : Addr → Int) →
      (source target : Addr) →
      (n : Int) →
      IfSet
        (intEqual n zeroZ)
        (lStrncmp scalar-memory source target n ≡ zeroZ)
        (IfSet
          (intEqual
            (scalar-memory (shift target zeroZ))
            (scalar-memory (shift source zeroZ)))
          (IfSet
            (intEqual
              (scalar-memory (shift source zeroZ))
              zeroZ)
            (lStrncmp scalar-memory source target n ≡ zeroZ)
            (lStrncmp
              scalar-memory
              (shift source oneZ)
              (shift target oneZ)
              (toUint64 conversion (subtractInt n oneZ))
              ≡ lStrncmp scalar-memory source target n))
          (toSint32 conversion
            (subtractInt
              (scalar-memory (shift source zeroZ))
              (scalar-memory (shift target zeroZ)))
            ≡ lStrncmp scalar-memory source target n))

    lStrncmp-in-range :
      (scalar-memory : Addr → Int) →
      (source target : Addr) →
      (n : Int) →
      IsSint32 (lStrncmp scalar-memory source target n)

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

PStrnEqual :
  {conversion : IntegerConversion} →
  StringOperations conversion →
  (Addr → Int) →
  Addr →
  Addr →
  Int →
  Set
PStrnEqual string-model scalar-memory source target n =
  lStrncmp string-model scalar-memory source target n ≡ zeroZ

Goal16 :
  (conversion : IntegerConversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal16 conversion string-model region linked sconst =
  (a : Addr) →
  (i : Int) →
  (a₁ : Addr) →
  (scalar-memory : Addr → Int) →
  (allocation : Int → Int) →
  let
    a₂ = shift a i
    a₃ = shift a₁ i
    x = lSysfsStrlen string-model scalar-memory a₂
  in
  scalar-memory a₂ ≡ tenZ →
  scalar-memory a₃ ≡ zeroZ →
  lSysfsStrlen string-model scalar-memory a₃ ≡ x →
  scalar-memory (shift a (addInt oneZ i)) ≡ zeroZ →
  i ≤Z lStrlen string-model scalar-memory a →
  i ≤Z lStrlen string-model scalar-memory a₁ →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  sconst scalar-memory →
  IsUint64 i →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₁ →
  PStrnEqual string-model scalar-memory a₁ a i →
  PValidString allocation scalar-memory a₂ →
  PValidString allocation scalar-memory a₃ →
  PStrnEqual string-model scalar-memory a₃ a₂ x →
  ((i₁ : Int) →
    zeroZ ≤Z i₁ →
    i₁ <Z i →
    scalar-memory (shift a₁ i₁) ≡ scalar-memory (shift a i₁)) →
  ((i₁ : Int) →
    let
      x₁ = scalar-memory (shift a i₁)
      x₂ = scalar-memory (shift a₁ i₁)
    in
    zeroZ ≤Z i₁ →
    i₁ <Z i →
    IsUint64 i₁ →
    (x₁ ≠ zeroZ) ∧
    (x₂ ≠ zeroZ) ∧
    (x₂ ≡ x₁)) →
  lSysfsStrlen string-model scalar-memory a ≡ i

sysfs-streq-assert-8-goal16 : Set₁
sysfs-streq-assert-8-goal16 =
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal16 conversion string-model region linked sconst
