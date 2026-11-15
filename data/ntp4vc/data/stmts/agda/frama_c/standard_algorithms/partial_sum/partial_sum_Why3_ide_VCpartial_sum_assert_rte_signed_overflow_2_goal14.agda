-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/partial_sum/partial_sum_Why3_ide_VCpartial_sum_assert_rte_signed_overflow_2_goal14:
-- under the stated accumulation, memory-update, range, validity, separation,
-- linkedness, and partial-sum assumptions, the next partial sum does not
-- exceed the signed 32-bit maximum. This file contains no proof.

{-# OPTIONS --safe #-}

module PartialSumGoal14 where

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

negateInt : Int → Int
negateInt (pos n) = negative n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

notBool : Bool → Bool
notBool true = false
notBool false = true

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

uint32Upper signed32Lower signed32Upper signed32Maximum : Int
uint32Upper = pos 4294967296
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
signed32Maximum = pos 2147483647

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

addrEqual : Addr → Addr → Bool
addrEqual (addr b o) (addr b′ o′) with intEqual b b′
... | false = false
... | true = intEqual o o′

update :
  {A : Set} →
  (Addr → A) →
  Addr →
  A →
  Addr →
  A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

separatedBool : Addr → Int → Addr → Int → Bool
separatedBool p a q b =
  orBool
    (intLessOrEqual a zeroZ)
    (orBool
      (intLessOrEqual b zeroZ)
      (orBool
        (notBool (intEqual (base p) (base q)))
        (orBool
          (intLessOrEqual (addInt (offset q) b) (offset p))
          (intLessOrEqual (addInt (offset p) a) (offset q)))))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b = separatedBool p a q b ≡ true

havoc :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Int
havoc old-memory new-memory start length location =
  ifBool
    (separatedBool location oneZ start length)
    (new-memory location)
    (old-memory location)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

ValidRD : (Int → Int) → Addr → Int → Set
ValidRD allocation p n =
  zeroZ <Z n →
  (zeroZ ≠ base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record Uint32Projection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (x : Int) →
      IsUint32 (toUint32 x)

    toUint32-identity :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

    toUint32-idempotent :
      (x : Int) →
      toUint32 (toUint32 x) ≡ toUint32 x

open Uint32Projection

PUnchanged :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PUnchanged memory₀ memory₁ start lower upper =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  memory₁ (shift start index) ≡ memory₀ (shift start index)

record AccumulateTheory : Set where
  field
    lAccumulate :
      (Addr → Int) →
      Addr →
      Int →
      Int →
      Int

    accumulate-in-range :
      (memory : Addr → Int) →
      (start : Addr) →
      (n init : Int) →
      IsSint32 (lAccumulate memory start n init)

    accumulate-empty :
      (n init : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      n ≤Z zeroZ →
      IsSint32 init →
      lAccumulate memory start n init ≡ init

    accumulate-next :
      (n init : Int) →
      (memory : Addr → Int) →
      (start : Addr) →
      zeroZ <Z n →
      IsSint32 init →
      addInt
        (memory (shift start (subtractInt n oneZ)))
        (lAccumulate memory start (subtractInt n oneZ) init)
        ≡ lAccumulate memory start n init

    accumulate-read :
      (init : Int) →
      (memory₀ memory₁ : Addr → Int) →
      (start : Addr) →
      (n : Int) →
      IsSint32 init →
      PUnchanged memory₀ memory₁ start zeroZ n →
      lAccumulate memory₁ start n init
        ≡ lAccumulate memory₀ start n init

open AccumulateTheory

PPartialSum :
  AccumulateTheory →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Set
PPartialSum accumulation memory input n output =
  (index : Int) →
  zeroZ ≤Z index →
  index <Z n →
  memory (shift output index)
    ≡ lAccumulate accumulation memory input (addInt oneZ index) zeroZ

PAccumulateBounds :
  AccumulateTheory →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PAccumulateBounds accumulation memory start n init =
  (index : Int) →
  index ≤Z n →
  zeroZ ≤Z index →
  let value = lAccumulate accumulation memory start index init
  in
  (signed32Lower ≤Z value) ∧
  (value ≤Z signed32Maximum)

Goal14 :
  Uint32Projection →
  AccumulateTheory →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal14 conversion accumulation region linked =
  (a a₁ : Addr) →
  (memory₂ memory₁ : Addr → Int) →
  (i i₁ : Int) →
  (allocation : Int → Int) →
  let
    a₂ = shift a zeroZ
    a₃ = shift a₁ zeroZ
    x = memory₂ a₃
    memory₄ =
      havoc
        memory₁
        (update memory₂ a₂ x)
        (shift a oneZ)
        (subtractInt i oneZ)
    x₁ = subtractInt i₁ oneZ
    a₅ = memory₄ (shift a x₁)
    a₆ = memory₄ (shift a₁ i₁)
    a₇ = memory₄ (shift a (toUint32 conversion x₁))
  in
  a₅ ≡ lAccumulate accumulation memory₄ a₁ i₁ zeroZ →
  zeroZ <Z i →
  zeroZ <Z i₁ →
  i₁ ≤Z i →
  i₁ <Z i →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsSint32 x →
  ValidRD allocation a₃ oneZ →
  ValidRD allocation a₃ i →
  ValidRW allocation a₂ oneZ →
  ValidRW allocation a₂ i →
  PAccumulateBounds
    accumulation
    memory₂
    a₁
    (addInt oneZ i)
    zeroZ →
  Separated a₃ i a₂ i →
  IsSint32 a₆ →
  IsSint32 a₅ →
  IsSint32 a₇ →
  PUnchanged memory₄ memory₂ a₁ zeroZ i →
  PPartialSum accumulation memory₄ a₁ i₁ a →
  addInt a₆ a₇ ≤Z signed32Maximum

partial-sum-assert-rte-signed-overflow-2-goal14 : Set₁
partial-sum-assert-rte-signed-overflow-2-goal14 =
  (conversion : Uint32Projection) →
  (accumulation : AccumulateTheory) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal14 conversion accumulation region linked
