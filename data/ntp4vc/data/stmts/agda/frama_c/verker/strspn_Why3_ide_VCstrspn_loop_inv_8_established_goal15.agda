-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strspn_Why3_ide_VCstrspn_loop_inv_8_established_goal15:
-- under the stated C memory, address-order, integer-range, string-validity,
-- linkedness, constancy, string-span, and prior-byte membership assumptions,
-- the byte at the designated accept-string address differs from the current
-- nonzero byte. This file contains no proof.

{-# OPTIONS --safe #-}

module StrspnWhy3IdeVCstrspnLoopInv8EstablishedGoal15 where

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

Goal15 :
  (conversion : IntegerConversion) →
  (order : AddressOrder) →
  StringOperations conversion order →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal15 conversion order string-model region linked sconst =
  (scalar-memory : Addr → Int) →
  (a₁ a a₃ : Addr) →
  (allocation : Int → Int) →
  (a₂ : Addr) →
  let
    x = scalar-memory a₁
    x₁ = offset a₁
    x₂ = offset a
    x₃ = lStrlen string-model scalar-memory a
  in
  x ≠ zeroZ →
  addInt x₁ (lStrspn string-model a₁ a₃)
    ≡ addInt x₂ (lStrspn string-model a a₃) →
  x₂ ≤Z x₁ →
  region (base a) ≤Z zeroZ →
  region (base a₃) ≤Z zeroZ →
  x₁ ≤Z addInt x₂ x₃ →
  linked allocation →
  sconst scalar-memory →
  addrLT order a₂ a₃ →
  addrLE order a a₁ →
  addrLE order a₃ a₂ →
  IsSint8 x →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₁ →
  PValidString allocation scalar-memory a₃ →
  IsUint64 (subtractInt x₁ x₂) →
  addrLE order a₁ (shift a x₃) →
  ((a₄ : Addr) →
    addrLT order a₄ a₁ →
    addrLE order a a₄ →
    Exists Addr
      (λ a₅ →
        (scalar-memory a₄ ≡ scalar-memory a₅) ∧
        addrLE order a₃ a₅ ∧
        addrLT order a₅
          (shift a₃ (lStrlen string-model scalar-memory a₃)))) →
  scalar-memory a₂ ≠ x

strspn-loop-invariant-8-established-goal15 : Set₁
strspn-loop-invariant-8-established-goal15 =
  (conversion : IntegerConversion) →
  (order : AddressOrder) →
  (string-model : StringOperations conversion order) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal15 conversion order string-model region linked sconst
