-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/replace_copy/replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0:
-- under the stated index bounds, memory-region, linkedness, integer-range,
-- validity, separation, unchanged-range, and replacement assumptions, reducing
-- the havoc range to the equal replacement length preserves the replace-copy
-- relation. This file contains no proof.

{-# OPTIONS --safe #-}

module replace_copy_Why3_ide_VCreplace_copy_post_replace_goal0 where

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

andBool : Bool → Bool → Bool
andBool true value = value
andBool false _ = false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false value = value

notBool : Bool → Bool
notBool true = false
notBool false = true

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true _ = when-true
ifValue false _ when-false = when-false

zeroZ oneZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)

uint32Upper signed32Lower signed32Upper : Int
uint32Upper = pos 4294967296
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

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
  ifValue
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

PUnchanged :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PUnchanged current-memory previous-memory start lower upper =
  (index : Int) →
  let location = shift start index
  in
  lower ≤Z index →
  index <Z upper →
  previous-memory location ≡ current-memory location

PReplace :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Int →
  Int →
  Set
PReplace source-memory destination-memory source length destination old-value new-value =
  (index : Int) →
  let
    source-entry = destination-memory (shift source index)
    destination-entry = source-memory (shift destination index)
  in
  zeroZ ≤Z index →
  index <Z length →
  (source-entry ≡ old-value → destination-entry ≡ new-value) ∧
  (source-entry ≠ old-value → destination-entry ≡ source-entry)

Goal0 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal0 region linked =
  (a₁ a : Addr) →
  (memory₁ memory₂ : Addr → Int) →
  (i₂ i₃ : Int) →
  (allocation : Int → Int) →
  (new-value old-value : Int) →
  let
    source-start = shift a₁ zeroZ
    destination-start = shift a zeroZ
    full-havoc = havoc memory₁ memory₂ destination-start i₂
  in
  i₃ ≤Z i₂ →
  zeroZ ≤Z i₃ →
  i₂ ≤Z i₃ →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  linked allocation →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsSint32 new-value →
  IsSint32 old-value →
  ValidRD allocation source-start i₂ →
  ValidRW allocation destination-start i₂ →
  Separated source-start i₂ a oneZ →
  PUnchanged full-havoc memory₂ a₁ i₃ i₂ →
  PReplace full-havoc memory₂ a₁ i₃ a old-value new-value →
  PReplace
    (havoc memory₁ memory₂ destination-start i₃)
    memory₂
    a₁
    i₃
    a
    old-value
    new-value

replace-copy-post-replace-goal0 : Set₁
replace-copy-post-replace-goal0 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal0 region linked
