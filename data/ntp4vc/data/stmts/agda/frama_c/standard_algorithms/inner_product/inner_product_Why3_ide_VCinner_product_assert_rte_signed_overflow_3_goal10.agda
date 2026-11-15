-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/inner_product/inner_product_Why3_ide_VCinner_product_assert_rte_signed_overflow_3_goal10:
-- under the stated index, memory, integer-range, product-bound, and partial
-- inner-product-bound assumptions, the next inner-product accumulation does
-- not underflow a signed 32-bit integer. This file contains no proof.

{-# OPTIONS --safe #-}

module inner-product-Why3-ide-VCinner-product-assert-rte-signed-overflow-3-goal10 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

zeroZ oneZ signed32Lower signed32Upper signed32Maximum uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648
signed32Maximum = pos 2147483647
uint32Upper = pos 4294967296

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

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

record Sint32Conversion : Set where
  field
    toSint32 : Int → Int

    resultInRange :
      (x : Int) →
      IsSint32 (toSint32 x)

    identityInRange :
      (x : Int) →
      IsSint32 x →
      toSint32 x ≡ x

    idempotent :
      (x : Int) →
      toSint32 (toSint32 x) ≡ toSint32 x

open Sint32Conversion

PUnchanged :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PUnchanged old-memory new-memory a lower upper =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  new-memory (shift a index) ≡ old-memory (shift a index)

record InnerProductTheory : Set where
  field
    lInnerProduct :
      (Addr → Int) →
      Addr →
      Addr →
      Int →
      Int →
      Int

    innerProductEmpty :
      (n initial : Int) →
      (memory : Addr → Int) →
      (a b : Addr) →
      n ≤Z zeroZ →
      IsSint32 initial →
      lInnerProduct memory a b n initial ≡ initial

    innerProductNext :
      (n initial : Int) →
      (memory : Addr → Int) →
      (a b : Addr) →
      zeroZ <Z n →
      IsSint32 initial →
      addInt
        (lInnerProduct memory a b (subtractInt n oneZ) initial)
        (multiplyInt
          (memory (shift a (subtractInt n oneZ)))
          (memory (shift b (subtractInt n oneZ))))
        ≡
        lInnerProduct memory a b n initial

    innerProductRead :
      (initial : Int) →
      (old-memory new-memory : Addr → Int) →
      (a : Addr) →
      (n : Int) →
      (b : Addr) →
      IsSint32 initial →
      PUnchanged old-memory new-memory a zeroZ n →
      PUnchanged old-memory new-memory b zeroZ n →
      lInnerProduct new-memory a b n initial ≡
        lInnerProduct old-memory a b n initial

open InnerProductTheory

PProductBounds :
  (Addr → Int) →
  Addr →
  Addr →
  Int →
  Set
PProductBounds memory a b n =
  (index : Int) →
  let product =
        multiplyInt
          (memory (shift a index))
          (memory (shift b index))
  in
  zeroZ ≤Z index →
  index <Z n →
  (signed32Lower ≤Z product) ∧
  (product ≤Z signed32Maximum)

PInnerProductBounds :
  InnerProductTheory →
  (Addr → Int) →
  Addr →
  Addr →
  Int →
  Int →
  Set
PInnerProductBounds theory memory a b n initial =
  (index : Int) →
  let partial = lInnerProduct theory memory a b index initial
  in
  index ≤Z n →
  zeroZ ≤Z index →
  (signed32Lower ≤Z partial) ∧
  (partial ≤Z signed32Maximum)

Goal10 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Sint32Conversion →
  InnerProductTheory →
  Set
Goal10 region linked conversion theory =
  (integer-memory : Addr → Int) →
  (a : Addr) →
  (i₂ : Int) →
  (a₁ : Addr) →
  (i₁ i : Int) →
  (allocation : Int → Int) →
  let
    x = integer-memory (shift a i₂)
    x₁ = integer-memory (shift a₁ i₂)
    x₂ = lInnerProduct theory integer-memory a₁ a i₂ i₁
  in
  i₂ ≤Z i →
  zeroZ ≤Z i₂ →
  i₂ <Z i →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₂ →
  IsSint32 i₁ →
  PProductBounds integer-memory a₁ a i →
  IsSint32 x →
  IsSint32 x₁ →
  PInnerProductBounds theory integer-memory a₁ a i i₁ →
  ValidRD allocation (shift a zeroZ) i →
  ValidRD allocation (shift a₁ zeroZ) i →
  IsSint32 x₂ →
  signed32Lower ≤Z
    addInt x₂ (toSint32 conversion (multiplyInt x x₁))

inner-product-assert-rte-signed-overflow-3-goal10 : Set₁
inner-product-assert-rte-signed-overflow-3-goal10 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Sint32Conversion) →
  (theory : InnerProductTheory) →
  Goal10 region linked conversion theory
