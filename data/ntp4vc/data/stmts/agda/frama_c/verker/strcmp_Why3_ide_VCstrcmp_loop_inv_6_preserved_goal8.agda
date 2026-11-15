-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strcmp_Why3_ide_VCstrcmp_loop_inv_6_preserved_goal8:
-- under the stated byte-conversion, string-comparison, address-order,
-- memory-validity, linkedness, constancy, and preceding-byte assumptions,
-- the successor offset and remaining second-string length equal the saved
-- end offset of the first string. This file contains no proof.

{-# OPTIONS --safe #-}

module StrcmpWhy3IdeVCstrcmpLoopInv6PreservedGoal8 where

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

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

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

zeroZ oneZ minusOneZ signed8Lower signed8Upper signed64Lower
  signed64Upper uint8Upper uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero
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

lCompare : IntegerConversion → Int → Int → Int
lCompare conversion a b =
  ifInt
    (intEqual b a)
    zeroZ
    (ifInt
      (intLess a b)
      minusOneZ
      oneZ)

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
        (intEqual n minusOneZ)
        (lStrncmp scalar-memory source target n ≡ zeroZ)
        (IfSet
          (intEqual
            (scalar-memory (shift target zeroZ))
            (scalar-memory (shift source zeroZ)))
          (lStrncmp
            scalar-memory
            (shift source oneZ)
            (shift target oneZ)
            (subtractInt n oneZ)
            ≡ lStrncmp scalar-memory source target n)
          (lCompare
            conversion
            (toUint8 conversion (scalar-memory (shift source zeroZ)))
            (toUint8 conversion (scalar-memory (shift target zeroZ)))
            ≡ lStrncmp scalar-memory source target n))

open StringOperations

lStrcmp :
  {conversion : IntegerConversion} →
  StringOperations conversion →
  (Addr → Int) →
  Addr →
  Addr →
  Int
lStrcmp string-model scalar-memory source target =
  lStrncmp
    string-model
    scalar-memory
    source
    target
    (lStrlen string-model scalar-memory source)

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

Goal8 :
  AddressOrder →
  (conversion : IntegerConversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal8 order conversion string-model region linked sconst =
  (scalar-memory : Addr → Int) →
  (a a₂ a₃ a₁ : Addr) →
  (allocation : Int → Int) →
  let
    x = scalar-memory a
    x₁ = toUint8 conversion x
    x₂ = scalar-memory a₂
    x₃ = offset a₂
    x₄ = offset a₃
    x₅ = lStrlen string-model scalar-memory a₃
    x₆ = addInt x₄ x₅
    x₇ = subtractInt x₃ x₄
    x₈ = scalar-memory (shift a₃ x₇)
    x₉ = scalar-memory (shift a₁ x₇)
  in
  x₁ ≠ zeroZ →
  toUint8 conversion x₂ ≡ x₁ →
  lStrcmp string-model scalar-memory a₃ a₁
    ≡ lStrcmp string-model scalar-memory a₂ a →
  addInt (offset a₁) x₃ ≡ addInt (offset a) x₄ →
  x₆ ≡ addInt x₃ (lStrlen string-model scalar-memory a₂) →
  x₈ ≡ x₉ →
  Iff
    ((i : Int) →
      zeroZ ≤Z i →
      i ≤Z x₅ →
      toUint8 conversion (scalar-memory (shift a₃ i))
        ≡ toUint8 conversion (scalar-memory (shift a₁ i)))
    ((i : Int) →
      zeroZ ≤Z i →
      i ≤Z x₅ →
      scalar-memory (shift a₃ i) ≡ scalar-memory (shift a₁ i)) →
  region (base a₁) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  linked allocation →
  sconst scalar-memory →
  addrLE order a₁ a →
  addrLE order a₃ a₂ →
  IsSint8 x →
  IsSint8 x₂ →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₁ →
  PValidString allocation scalar-memory a₂ →
  PValidString allocation scalar-memory a₃ →
  addrLE order a
    (shift a₁ (lStrlen string-model scalar-memory a₁)) →
  addrLE order a₂ (shift a₃ x₅) →
  IsSint8 x₉ →
  IsSint8 x₈ →
  ((i : Int) →
    zeroZ ≤Z i →
    addInt i x₄ <Z x₃ →
    scalar-memory (shift a₃ i) ≡ scalar-memory (shift a₁ i)) →
  addInt
    (addInt oneZ x₃)
    (lStrlen string-model scalar-memory (shift a₂ oneZ))
    ≡ x₆

strcmp-loop-invariant-6-preserved-goal8 : Set₁
strcmp-loop-invariant-6-preserved-goal8 =
  (order : AddressOrder) →
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal8 order conversion string-model region linked sconst
