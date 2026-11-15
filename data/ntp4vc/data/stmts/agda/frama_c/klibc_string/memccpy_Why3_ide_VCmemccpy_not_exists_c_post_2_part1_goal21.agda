-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/klibc_string/memccpy_Why3_ide_VCmemccpy_not_exists_c_post_2_part1_goal21:
-- after the specified scalar-memory havoc and update, the source and
-- destination bytes at the selected index are equal under the stated integer
-- bounds, memory validity, separation, address-order, linkedness, constancy,
-- copy-prefix, and byte-nonoccurrence assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module memccpy-Why3-ide-VCmemccpy-not-exists-c-post-2-part1-goal21 where

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

andBool : Bool → Bool → Bool
andBool true value = value
andBool false _ = false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false value = value

notBool : Bool → Bool
notBool true = false
notBool false = true

ifBool : {A : Set} → Bool → A → A → A
ifBool true when-true _ = when-true
ifBool false _ when-false = when-false

zeroZ oneZ signedByteLower signedByteUpper uint32Upper
  signed32Lower signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
signedByteLower = negsuc 127
signedByteUpper = pos 127
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

addrEqual : Addr → Addr → Bool
addrEqual p q =
  andBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
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
havoc old-memory new-memory location size query =
  ifBool
    (separatedBool query oneZ location size)
    (new-memory query)
    (old-memory query)

AddrLE : Addr → Addr → Set
AddrLE p q = offset p ≤Z offset q

ValidRW : (Int → Int) → Addr → Int → Set
ValidRW allocation p n =
  zeroZ <Z n →
  (zeroZ <Z base p) ∧
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

toSint8 : Int → Int
toSint8 x = x

Goal21 :
  (Int → Int) →
  ((Int → Int) → Set) →
  ((Addr → Int) → Set) →
  Set
Goal21 region linked sconst =
  (a₁ : Addr) →
  (i₁ i : Int) →
  (t₁ t₂ : Addr → Int) →
  (a : Addr) →
  (i₃ i₂ : Int) →
  (allocation : Int → Int) →
  let
    a₂ = shift a₁ zeroZ
    x = subtractInt i₁ i
    a₃ = havoc t₁ t₂ a₂ x
    a₄ = shift a x
    a₅ = a₃ a₄
    a₆ = shift a zeroZ
    a₇ = shift a₁ x
    a₈ = update a₃ a₇ a₅
  in
  i ≠ zeroZ →
  a₅ ≡ toSint8 i₃ →
  zeroZ <Z i₁ →
  zeroZ ≤Z i →
  i ≤Z i₁ →
  zeroZ ≤Z i₂ →
  i₂ <Z i₁ →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  signedByteLower ≤Z i₃ →
  i₃ ≤Z signedByteUpper →
  linked allocation →
  sconst t₂ →
  IsUint32 i →
  IsUint32 i₁ →
  IsSint32 i₃ →
  ValidRW allocation a₆ i₁ →
  ValidRW allocation a₂ i₁ →
  Separated a₆ i₁ a₂ i₁ →
  AddrLE a a₄ →
  AddrLE a₁ a₇ →
  AddrLE a₄ (shift a i₁) →
  AddrLE a₇ (shift a₁ i₁) →
  ((i₄ : Int) →
    zeroZ ≤Z i₄ →
    addInt i₄ i <Z i₁ →
    a₃ (shift a₁ i₄) ≡ a₃ (shift a i₄)) →
  ((i₄ : Int) →
    zeroZ ≤Z i₄ →
    i₄ <Z i₁ →
    a₅ ≠ t₂ (shift a i₄)) →
  ((i₄ : Int) →
    zeroZ ≤Z i₄ →
    addInt i₄ i <Z i₁ →
    a₅ ≠ a₃ (shift a₁ i₄)) →
  a₈ (shift a₁ i₂) ≡ a₈ (shift a i₂)

memccpy-not-exists-c-post-2-part1-goal21 : Set₁
memccpy-not-exists-c-post-2-part1-goal21 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (sconst : (Addr → Int) → Set) →
  Goal21 region linked sconst
