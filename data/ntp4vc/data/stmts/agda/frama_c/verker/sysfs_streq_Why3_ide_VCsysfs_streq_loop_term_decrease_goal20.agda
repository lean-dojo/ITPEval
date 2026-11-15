-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/sysfs_streq_Why3_ide_VCsysfs_streq_loop_term_decrease_goal20:
-- decrease of the sysfs_streq loop variant: under the stated memory,
-- string-validity, integer-range, linkedness, constancy, string-equality,
-- and equal-prefix assumptions, the current index is strictly less than
-- the unsigned-64 conversion of its successor. This file contains no proof.

{-# OPTIONS --safe #-}

module sysfs_streq_Why3_ide_VCsysfs_streq_loop_term_decrease_goal20 where

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
    toSint32 : Int → Int
    toUint64 : Int → Int

    toSint32-in-range :
      (x : Int) →
      IsSint32 (toSint32 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toSint32-identity :
      (x : Int) →
      IsSint32 x →
      toSint32 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toSint32-idempotent :
      (x : Int) →
      toSint32 (toSint32 x) ≡ toSint32 x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

open IntegerConversion

record StringOperations (conversion : IntegerConversion) : Set where
  field
    lStrlen  : (Addr → Int) → Addr → Int
    lStrncmp : (Addr → Int) → Addr → Addr → Int → Int

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

Goal20 :
  (conversion : IntegerConversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal20 conversion string-model region linked sconst =
  (a₁ : Addr) →
  (i : Int) →
  (scalar-memory : Addr → Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  let
    a₂ = shift a₁ i
    x = scalar-memory a₂
    a₃ = shift a i
    x₁ = scalar-memory a₃
  in
  x ≠ zeroZ →
  x ≡ x₁ →
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
  IsSint8 x₁ →
  IsSint8 x →
  PValidString allocation scalar-memory a₃ →
  PValidString allocation scalar-memory a₂ →
  ((i₁ : Int) →
    zeroZ ≤Z i₁ →
    i₁ <Z i →
    scalar-memory (shift a₁ i₁) ≡ scalar-memory (shift a i₁)) →
  i <Z toUint64 conversion (addInt oneZ i)

sysfs-streq-loop-term-decrease-goal20 : Set₁
sysfs-streq-loop-term-decrease-goal20 =
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal20 conversion string-model region linked sconst
