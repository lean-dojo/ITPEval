-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/reverse/reverse_Why3_ide_VCreverse_loop_inv_right_preserved_goal7:
-- under the stated integer-range, memory-validity, linkedness, unchanged-region,
-- and partial-reversal invariants, swapping the two selected cells preserves the
-- right-hand reversal invariant. This file contains no proof.

{-# OPTIONS --safe #-}

module reverse-Why3-ide-VCreverse-loop-inv-right-preserved-goal7 where

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

ifBool : {A : Set} → Bool → A → A → A
ifBool true when-true when-false = when-true
ifBool false when-true when-false = when-false

notBool : Bool → Bool
notBool true = false
notBool false = true

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false value = value

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
negateInt (pos zero) = pos zero
negateInt (pos (suc n)) = negsuc n
negateInt (negsuc n) = pos (suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

halfNat : Nat → Nat
halfNat zero = zero
halfNat (suc zero) = zero
halfNat (suc (suc n)) = suc (halfNat n)

negativeNat : Nat → Int
negativeNat zero = pos zero
negativeNat (suc n) = negsuc n

cdivTwo : Int → Int
cdivTwo (pos n) = pos (halfNat n)
cdivTwo (negsuc n) = negativeNat (halfNat (suc n))

zeroZ oneZ uint32Maximum uint32MaximumMinusOne uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
uint32Maximum = pos 4294967295
uint32MaximumMinusOne = pos 4294967294
uint32Upper = pos 4294967296

signed32Lower signed32Upper : Int
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

addrEqual : Addr → Addr → Bool
addrEqual p q =
  ifBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))
    false

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

update : (Addr → Int) → Addr → Int → Addr → Int
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

havoc :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Int
havoc memory₀ memory₁ start length location =
  ifBool
    (separatedBool location oneZ start length)
    (memory₁ location)
    (memory₀ location)

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
  (zeroZ ≤Z offset p) ∧
  (addInt (offset p) n ≤Z allocation (base p))

IsUint32 : Int → Set
IsUint32 value =
  (zeroZ ≤Z value) ∧
  (value <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 value =
  (signed32Lower ≤Z value) ∧
  (value <Z signed32Upper)

record Uint32Projection : Set where
  field
    toUint32 : Int → Int

    toUint32-in-range :
      (value : Int) →
      IsUint32 (toUint32 value)

    toUint32-identity :
      (value : Int) →
      IsUint32 value →
      toUint32 value ≡ value

open Uint32Projection

PReverse1 :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Set
PReverse1 memory₀ memory₁ a n b =
  (index : Int) →
  zeroZ ≤Z index →
  index <Z n →
  memory₀
    (shift b (subtractInt (subtractInt n oneZ) index))
    ≡
  memory₁ (shift a index)

PReverse2 :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Addr →
  Int →
  Set
PReverse2 memory₀ memory₁ a m n b p =
  PReverse1
    memory₀
    memory₁
    (shift a m)
    (subtractInt n m)
    (shift b p)

PReverse4 :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PReverse4 memory₀ memory₁ a m n p =
  PReverse2 memory₀ memory₁ a m n a p

PUnchanged1 :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PUnchanged1 memory₀ memory₁ a m n =
  (index : Int) →
  let location = shift a index
  in
  m ≤Z index →
  index <Z n →
  memory₁ location ≡ memory₀ location

Goal7 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal7 conversion region linked =
  (a : Addr) →
  (memory₀ memory₁ : Addr → Int) →
  (i₁ i₂ replacement : Int) →
  (allocation : Int → Int) →
  let
    a₁ = shift a zeroZ
    memory₂ = havoc memory₀ memory₁ a₁ i₁
    x₁ = subtractInt (subtractInt i₁ oneZ) i₂
    a₃ = shift a x₁
    a₄ = shift a i₂
    a₅ = memory₂ a₃
    memory₆ = update (update memory₂ a₃ replacement) a₄ a₅
    a₇ = memory₆ a₃
    a₈ = memory₂ a₄
    x₂ = cdivTwo i₁
    x₃ = toUint32 conversion (subtractInt i₁ oneZ)
    x₄ = subtractInt i₁ i₂
  in
  a₇ ≡ a₈ →
  zeroZ <Z i₁ →
  zeroZ ≤Z i₂ →
  i₂ <Z x₂ →
  i₂ ≤Z x₂ →
  region (base a) ≤Z zeroZ →
  addInt i₂ x₂ ≤Z i₁ →
  i₂ ≤Z x₃ →
  i₂ ≤Z uint32MaximumMinusOne →
  x₃ ≤Z addInt uint32Maximum i₂ →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 x₂ →
  IsUint32 (addInt oneZ i₂) →
  ValidRW allocation a₁ i₁ →
  ValidRW allocation a₄ oneZ →
  IsSint32 a₈ →
  IsSint32 a₅ →
  ValidRW allocation a₃ oneZ →
  IsSint32 a₇ →
  PUnchanged1 memory₂ memory₁ a i₂ x₄ →
  PReverse4 memory₂ memory₁ a zeroZ i₂ x₄ →
  PReverse4 memory₂ memory₁ a x₄ i₁ zeroZ →
  PReverse4 memory₆ memory₁ a x₁ i₁ zeroZ

reverse-loop-invariant-right-preserved-goal7 : Set₁
reverse-loop-invariant-right-preserved-goal7 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal7 conversion region linked
