-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/remove_copy/remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5:
-- under the stated loop bounds, integer-range, memory-validity, separation,
-- unchanged-memory, and multiset-retention assumptions for remove_copy, the
-- next loop state retains the required multiplicities of every value other
-- than the removed value. This file contains no proof.

{-# OPTIONS --safe #-}

module remove_copy_Why3_ide_VCremove_copy_loop_inv_retain_preserved_goal5 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≠_ _≗_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

_≗_ : {A B : Set} → (A → B) → (A → B) → Set
_≗_ {A = A} left right =
  (x : A) →
  left x ≡ right x

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

ifSet : Bool → Set → Set → Set
ifSet true when-true _ = when-true
ifSet false _ when-false = when-false

ifValue : {A : Set} → Bool → A → A → A
ifValue true when-true _ = when-true
ifValue false _ when-false = when-false

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

zeroZ oneZ uint32Upper uint32MaximumMinusOne : Int
zeroZ = pos zero
oneZ = pos (suc zero)
uint32Upper = pos 4294967296
uint32MaximumMinusOne = pos 4294967294

signed32Lower signed32Upper : Int
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
  ifValue (addrEqual query location) value (memory query)

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
havoc old-memory new-memory location size query =
  ifValue
    (separatedBool query oneZ location size)
    (new-memory query)
    (old-memory query)

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

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  ifSet (separatedBool p a q b) (zeroZ ≡ zeroZ) Bottom

IsUint32 : Int → Set
IsUint32 x =
  (zeroZ ≤Z x) ∧
  (x <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

PHasValue :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PHasValue memory a lower upper sought =
  Exists Int λ index →
    (memory (shift a index) ≡ sought) ∧
    (lower ≤Z index) ∧
    (index <Z upper)

PUnchanged :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PUnchanged current-memory previous-memory a lower upper =
  (index : Int) →
  let location = shift a index
  in
  lower ≤Z index →
  index <Z upper →
  previous-memory location ≡ current-memory location

record CountOperations : Set where
  field
    lCount :
      (Addr → Int) →
      Addr →
      Int →
      Int →
      Int →
      Int

    countSectionEmpty :
      (upper lower value : Int) →
      (integer-memory : Addr → Int) →
      (a : Addr) →
      upper ≤Z lower →
      IsSint32 value →
      lCount integer-memory a lower upper value ≡ zeroZ

    countSectionHit :
      (upper : Int) →
      (integer-memory : Addr → Int) →
      (a : Addr) →
      (value lower : Int) →
      integer-memory (shift a (subtractInt upper oneZ)) ≡ value →
      lower <Z upper →
      IsSint32 value →
      addInt oneZ
        (lCount integer-memory a lower (subtractInt upper oneZ) value)
        ≡
      lCount integer-memory a lower upper value

    countSectionMiss :
      (upper : Int) →
      (integer-memory : Addr → Int) →
      (a : Addr) →
      (value lower : Int) →
      integer-memory (shift a (subtractInt upper oneZ)) ≠ value →
      lower <Z upper →
      IsSint32 value →
      lCount integer-memory a lower (subtractInt upper oneZ) value
        ≡
      lCount integer-memory a lower upper value

    countSectionRead :
      (value : Int) →
      (current-memory previous-memory : Addr → Int) →
      (a : Addr) →
      (lower upper : Int) →
      IsSint32 value →
      PUnchanged current-memory previous-memory a lower upper →
      lCount previous-memory a lower upper value
        ≡
      lCount current-memory a lower upper value

open CountOperations

PMultisetRetainRest :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Addr →
  Int →
  Int →
  Int →
  Set
PMultisetRetainRest
  counts current-memory reference-memory
  source lower-source upper-source
  destination lower-destination upper-destination
  excluded-value =
  (value : Int) →
  value ≠ excluded-value →
  IsSint32 value →
  lCount counts
    reference-memory source lower-source upper-source value
    ≡
  lCount counts
    current-memory destination lower-destination upper-destination value

Goal5 :
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal5 region linked counts =
  (t₃ : Addr → Int) →
  (a₁ : Addr) →
  (i₅ i : Int) →
  (a : Addr) →
  (t₁ : Addr → Int) →
  (i₂ : Int) →
  (allocation : Int → Int) →
  (i₁ i₃ i₄ : Int) →
  (t₂ : Addr → Int) →
  (p : Bool) →
  let
    x = lCount counts t₃ a₁ zeroZ i₅ i
    x₁ = addInt oneZ i₅
    a₂ = shift a₁ zeroZ
    a₃ = shift a₁ i₅
    a₄ = shift a zeroZ
    x₂ = subtractInt i₅ x
    a₅ = havoc t₁ t₃ a₄ i₂
    a₆ = a₅ a₃
    a₇ = shift a x₂
  in
  i₅ ≤Z i₂ →
  i₅ <Z i₂ →
  region (base a) ≤Z zeroZ →
  region (base a₁) ≤Z zeroZ →
  x ≤Z i₅ →
  zeroZ ≤Z x →
  i₅ ≤Z uint32MaximumMinusOne →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsUint32 i₄ →
  IsUint32 i₅ →
  IsSint32 i →
  IsUint32 x₁ →
  ValidRD allocation a₂ i₂ →
  ValidRD allocation a₃ oneZ →
  ValidRW allocation a₄ i₂ →
  Separated a₂ i₂ a oneZ →
  IsUint32 x₂ →
  IsSint32 a₆ →
  Not (PHasValue a₅ a zeroZ x₂ i) →
  PUnchanged a₅ t₃ a₁ i₅ i₂ →
  PUnchanged a₅ t₃ a x₂ i₂ →
  PMultisetRetainRest
    counts a₅ t₃ a₁ zeroZ i₅ a zeroZ x₂ i →
  ifSet
    (intEqual a₆ i)
    ((a₅ ≗ t₂) ∧
      (addInt i₄
        (lCount counts t₃ a₁ zeroZ i₅ (t₂ a₃))
        ≡
      i₅))
    ((p ≡ false) ∧
      (i₃ ≡ i₁) ∧
      (addInt i₁ x ≡ i₅) ∧
      (addInt i₃ x ≡ i₅) ∧
      (addInt i₄ x ≡ x₁) ∧
      (update a₅ a₇ a₆ ≗ t₂) ∧
      (i₅ ≤Z addInt uint32MaximumMinusOne x) ∧
      ValidRW allocation a₇ oneZ) →
  PMultisetRetainRest
    counts t₂ t₃ a₁ zeroZ x₁ a zeroZ i₄ i

remove-copy-loop-inv-retain-preserved-goal5 : Set₁
remove-copy-loop-inv-retain-preserved-goal5 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal5 region linked counts
