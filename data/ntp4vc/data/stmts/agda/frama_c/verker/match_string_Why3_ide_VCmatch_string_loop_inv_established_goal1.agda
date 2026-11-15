-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/match_string_Why3_ide_VCmatch_string_loop_inv_established_goal1:
-- under the stated C memory, integer-range, framing, linkedness, and
-- string-validity assumptions, the real array length is nonnegative and at
-- most the supplied bound. This file contains no proof.

{-# OPTIONS --safe #-}

module MatchStringWhy3IdeVCMatchStringLoopInvEstablishedGoal1 where

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    evidence : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false value = value

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

zeroZ oneZ signed8Lower signed8Upper signed32Maximum uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signed8Lower = negsuc 127
signed8Upper = pos 128
signed32Maximum = pos 2147483647
uint64Upper = pos 18446744073709551616

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

zeroAddr : Addr
zeroAddr = addr zeroZ zeroZ

addrEqual : Addr → Addr → Bool
addrEqual (addr base-left offset-left) (addr base-right offset-right) =
  compare-base
  where
  compare-base : Bool
  compare-base with intEqual base-left base-right
  ... | true = intEqual offset-left offset-right
  ... | false = false

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

Framed : (Int → Int) → (Addr → Addr) → Set
Framed region pointer-memory =
  (p : Addr) →
  region (base (pointer-memory p)) ≤Z zeroZ

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

record MatchOperations (conversion : Uint64Conversion) : Set where
  field
    lRealLen : (Addr → Addr) → Addr → Int → Int

    lRealLen-fix :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (n : Int) →
      IfSet
        (orBool
          (intEqual n zeroZ)
          (addrEqual (pointer-memory (shift array zeroZ)) zeroAddr))
        (lRealLen pointer-memory array n ≡ zeroZ)
        (toUint64 conversion
          (addInt oneZ
            (lRealLen
              pointer-memory
              (shift array oneZ)
              (toUint64 conversion (subtractInt n oneZ))))
          ≡ lRealLen pointer-memory array n)

    lRealLen-in-range :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (n : Int) →
      IsUint64 (lRealLen pointer-memory array n)

open MatchOperations

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
  (conversion : Uint64Conversion) →
  MatchOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal1 conversion match-model region linked sconst =
  (pointer-memory : Addr → Addr) →
  (a₁ : Addr) →
  (i : Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  (scalar-memory : Addr → Int) →
  let
    x = lRealLen match-model pointer-memory a₁ i
    a₂ = shift a₁ zeroZ
  in
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  i ≤Z signed32Maximum →
  Framed region pointer-memory →
  linked allocation →
  sconst scalar-memory →
  IsUint64 i →
  PValidString allocation scalar-memory a →
  (x ≡ i →
    ValidRW allocation a₂ i) →
  (x <Z i →
    ValidRW allocation a₂ (addInt oneZ x)) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z x →
    IsUint64 index →
    PValidString
      allocation
      scalar-memory
      (pointer-memory (shift a₁ index))) →
  (x ≤Z i) ∧
  (zeroZ ≤Z x)

match-string-loop-inv-established-goal1 : Set₁
match-string-loop-inv-established-goal1 =
  (conversion : Uint64Conversion) →
  (match-model : MatchOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal1
    conversion
    match-model
    region
    linked
    sconst
