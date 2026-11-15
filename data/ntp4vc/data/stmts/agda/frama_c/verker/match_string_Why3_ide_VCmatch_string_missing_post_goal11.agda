-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/verker/match_string_Why3_ide_VCmatch_string_missing_post_goal11:
-- under the stated C memory, integer-range, framing, linkedness,
-- string-comparison, string-validity, prior-array-entry, and byte-agreement
-- assumptions, the missing match-string result is -22. This file contains no proof.

{-# OPTIONS --safe #-}

module match_string_Why3_ide_VCmatch_string_missing_post_goal11 where

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

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

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

zeroZ oneZ minusOneZ minusTwentyTwoZ signed8Lower signed8Upper
  signed32Lower signed32Upper signed32Maximum uint8Upper uint64Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero
minusTwentyTwoZ = negsuc 21
signed8Lower = negsuc 127
signed8Upper = pos 128
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
signed32Maximum = pos 2147483647
uint8Upper = pos 256
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

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

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
    toUint64 : Int → Int

    toUint8-in-range :
      (x : Int) →
      IsUint8 (toUint8 x)

    toUint64-in-range :
      (x : Int) →
      IsUint64 (toUint64 x)

    toUint8-identity :
      (x : Int) →
      IsUint8 x →
      toUint8 x ≡ x

    toUint64-identity :
      (x : Int) →
      IsUint64 x →
      toUint64 x ≡ x

    toUint8-idempotent :
      (x : Int) →
      toUint8 (toUint8 x) ≡ toUint8 x

    toUint64-idempotent :
      (x : Int) →
      toUint64 (toUint64 x) ≡ toUint64 x

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
    lStrlen : (Addr → Int) → Addr → Int
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

record MatchOperations (conversion : IntegerConversion) : Set where
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

Goal11 :
  (conversion : IntegerConversion) →
  StringOperations conversion →
  MatchOperations conversion →
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal11 conversion string-model match-model region linked sconst =
  (pointer-memory : Addr → Addr) →
  (a₁ : Addr) →
  (i₁ : Int) →
  (i : Int) →
  (scalar-memory : Addr → Int) →
  (a : Addr) →
  (allocation : Int → Int) →
  let
    a₂ = pointer-memory (shift a₁ i₁)
    x = lRealLen match-model pointer-memory a₁ i
    a₃ = shift a₁ zeroZ
  in
  a₂ ≠ zeroAddr →
  lStrcmp string-model scalar-memory a₂ a ≡ zeroZ →
  zeroZ ≤Z i₁ →
  toUint64 conversion i₁ <Z i →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  x ≤Z i →
  i₁ ≤Z x →
  i ≤Z signed32Maximum →
  Framed region pointer-memory →
  linked allocation →
  sconst scalar-memory →
  IsSint32 i₁ →
  IsUint64 i →
  PValidString allocation scalar-memory a →
  PValidString allocation scalar-memory a₂ →
  (x ≡ i →
    ValidRW allocation a₃ i) →
  (x <Z i →
    ValidRW allocation a₃ (addInt oneZ x)) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z i₁ →
    PValidString
      allocation
      scalar-memory
      (pointer-memory (shift a₁ index))) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z i₁ →
    lStrcmp
      string-model
      scalar-memory
      (pointer-memory (shift a₁ index))
      a
      ≠ zeroZ) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z x →
    IsUint64 index →
    PValidString
      allocation
      scalar-memory
      (pointer-memory (shift a₁ index))) →
  ((index : Int) →
    zeroZ ≤Z index →
    index <Z x →
    IsUint64 index →
    lStrcmp
      string-model
      scalar-memory
      (pointer-memory (shift a₁ index))
      a
      ≠ zeroZ) →
  ((index : Int) →
    Either
      (scalar-memory (shift a₂ index)
        ≡ scalar-memory (shift a index))
      (Either
        (index <Z zeroZ)
        (lStrlen string-model scalar-memory a₂ <Z index))) →
  i₁ ≡ minusTwentyTwoZ

match-string-missing-post-goal11 : Set₁
match-string-missing-post-goal11 =
  (conversion : IntegerConversion) →
  (string-model : StringOperations conversion) →
  (match-model : MatchOperations conversion) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal11
    conversion
    string-model
    match-model
    region
    linked
    sconst
