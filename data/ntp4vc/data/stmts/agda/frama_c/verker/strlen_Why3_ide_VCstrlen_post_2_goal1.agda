-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/strlen_Why3_ide_VCstrlen_post_2_goal1:
-- under the stated C memory, string-validity, address-order, integer-range,
-- linkedness, constancy, and length-offset assumptions, the byte selected by
-- the unsigned offset from the string start is zero. This file contains no
-- proof.

{-# OPTIONS --safe #-}

module StrlenWhy3IdeVCstrlenPost2Goal1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

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

    addrLE-same-base :
      (p q : Addr) →
      base p ≡ base q →
      Iff (addrLE p q) (offset p ≤Z offset q)

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

record StringOperations (conversion : IntegerConversion) : Set where
  field
    lStrlen : (Addr → Int) → Addr → Int

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

Goal1 :
  AddressOrder →
  (conversion : IntegerConversion) →
  StringOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal1 order conversion string-model region linked sconst =
  (a₁ : Addr) →
  (scalar-memory : Addr → Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  let
    start-offset = offset a₁
    string-length = lStrlen string-model scalar-memory a₁
    current-offset = offset a
    selected-byte =
      scalar-memory
        (shift a₁
          (toUint64 conversion (subtractInt current-offset start-offset)))
  in
  scalar-memory a ≡ zeroZ →
  addInt start-offset string-length
    ≡ addInt current-offset (lStrlen string-model scalar-memory a) →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  sconst scalar-memory →
  addrLE order a₁ a →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₁ →
  addrLE order a (shift a₁ string-length) →
  IsSint8 selected-byte →
  selected-byte ≡ zeroZ

strlen-post-2-goal1 : Set₁
strlen-post-2-goal1 =
  (order : AddressOrder) →
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal1 order conversion string-model region linked sconst
