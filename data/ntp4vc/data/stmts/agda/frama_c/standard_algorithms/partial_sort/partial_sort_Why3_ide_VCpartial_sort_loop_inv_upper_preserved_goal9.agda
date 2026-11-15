-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_loop_inv_upper_preserved_goal9:
-- under the stated index, memory-validity, heap, multiset, unchanged-region,
-- maximum-element, swap, and lower-bound assumptions, the value produced by
-- the final havoc update is an upper bound for the heap prefix.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module partial_sort_Why3_ide_VCpartial_sort_loop_inv_upper_preserved_goal9 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper)

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

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

truncateDivide : Int → Int → Int
truncateDivide (pos n) (pos zero) = pos zero
truncateDivide (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
truncateDivide (pos n) (negsuc m) =
  negative (natDivide n (suc m))
truncateDivide (negsuc n) (pos zero) = pos zero
truncateDivide (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
truncateDivide (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

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

zeroZ oneZ twoZ uint32Upper uint32MaximumMinusOne : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
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
  ifBool
    (separatedBool query oneZ location size)
    (new-memory query)
    (old-memory query)

updateMemory :
  (Addr → Int) →
  Addr →
  Int →
  Addr →
  Int
updateMemory integer-memory location value query =
  ifBool
    (addrEqual query location)
    value
    (integer-memory query)

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
IsUint32 value =
  (zeroZ ≤Z value) ∧
  (value <Z uint32Upper)

IsSint32 : Int → Set
IsSint32 value =
  (signed32Lower ≤Z value) ∧
  (value <Z signed32Upper)

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

PMultisetUnchanged :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMultisetUnchanged counts current-memory previous-memory a lower upper =
  (value : Int) →
  IsSint32 value →
  lCount counts previous-memory a lower upper value
    ≡
  lCount counts current-memory a lower upper value

heapParent : Int → Int
heapParent index =
  truncateDivide (subtractInt index oneZ) twoZ

PIsHeap :
  (Addr → Int) →
  Addr →
  Int →
  Set
PIsHeap integer-memory a upper =
  (index : Int) →
  zeroZ <Z index →
  index <Z upper →
  integer-memory (shift a index)
    ≤Z
  integer-memory (shift a (heapParent index))

PUpperBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PUpperBound integer-memory a lower upper value =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  integer-memory (shift a index) ≤Z value

PLowerBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PLowerBound integer-memory a lower upper value =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  value ≤Z integer-memory (shift a index)

PMaxElement :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMaxElement integer-memory a upper maximum-index =
  (zeroZ ≤Z maximum-index) ∧
  (maximum-index <Z upper) ∧
  PUpperBound
    integer-memory
    a
    zeroZ
    upper
    (integer-memory (shift a maximum-index))

PSwappedInside :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PSwappedInside current-memory previous-memory a first-index second-index upper =
  let
    first-location = shift a first-index
    second-location = shift a second-index
  in
  (previous-memory first-location ≡ current-memory second-location) ∧
  (previous-memory second-location ≡ current-memory first-location) ∧
  (zeroZ ≤Z first-index) ∧
  (first-index <Z second-index) ∧
  (second-index <Z upper) ∧
  PUnchanged current-memory previous-memory a zeroZ first-index ∧
  PUnchanged
    current-memory
    previous-memory
    a
    (addInt oneZ first-index)
    second-index ∧
  PUnchanged
    current-memory
    previous-memory
    a
    (addInt oneZ second-index)
    upper

Goal9 :
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal9 region linked counts =
  (a : Addr) →
  (t₁ t₅ : Addr → Int) →
  (i₂ : Int) →
  (t₂ : Addr → Int) →
  (i₁ : Int) →
  (t₃ : Addr → Int) →
  (i₃ i : Int) →
  (t₄ : Addr → Int) →
  (allocation : Int → Int) →
  let
    a₁ = shift a zeroZ
    a₂ = havoc t₁ t₅ a₁ i₂
    a₃ = havoc t₂ a₂ a₁ i₁
    a₄ = havoc t₃ a₃ a₁ i₂
    x = subtractInt i₂ oneZ
    a₅ = shift a x
    a₆ = a₄ a₅
    a₇ = a₃ a₁
    a₈ = shift a i₃
    a₉ = a₄ a₈
    a₁₀ = updateMemory (updateMemory a₄ a₈ i) a₅ a₉
    a₁₁ = a₁₀ a₈
    a₁₂ = a₃ a₈
    x₁ = addInt oneZ i₃
    a₁₃ = havoc t₄ a₁₀ a₁ i₂
    a₁₄ = a₁₃ a₁
  in
  a₆ ≡ a₇ →
  a₁₁ ≡ a₆ →
  zeroZ <Z i₂ →
  i₂ ≤Z i₁ →
  i₃ ≤Z i₁ →
  zeroZ ≤Z i₂ →
  i₃ <Z i₁ →
  i₂ ≤Z i₃ →
  region (base a) ≤Z zeroZ →
  a₁₂ <Z a₇ →
  i₃ ≤Z uint32MaximumMinusOne →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  ValidRD allocation a₁ oneZ →
  ValidRD allocation a₈ oneZ →
  ValidRW allocation a₁ i₁ →
  ValidRW allocation a₁ i₂ →
  ValidRW allocation a₈ oneZ →
  ValidRW allocation a₅ oneZ →
  IsSint32 (a₂ a₁) →
  PIsHeap a₂ a i₂ →
  PMultisetUnchanged counts a₂ t₅ a zeroZ i₂ →
  IsSint32 a₇ →
  IsSint32 a₁₂ →
  PIsHeap a₃ a i₂ →
  PMultisetUnchanged counts a₃ t₅ a zeroZ i₃ →
  PUnchanged a₃ t₅ a i₃ i₁ →
  PUpperBound a₃ a zeroZ i₂ a₇ →
  PLowerBound a₃ a i₂ i₃ a₇ →
  IsSint32 a₉ →
  IsSint32 a₆ →
  PIsHeap a₄ a x →
  IsSint32 a₁₁ →
  PMultisetUnchanged counts a₄ t₅ a zeroZ x₁ →
  PMultisetUnchanged counts a₄ a₃ a zeroZ i₂ →
  PMaxElement a₄ a i₂ x →
  PIsHeap a₁₀ a x →
  PMultisetUnchanged counts a₁₀ a₄ a zeroZ x₁ →
  PUnchanged a₁₀ a₄ a x₁ i₁ →
  PSwappedInside a₁₀ a₄ a x i₃ x₁ →
  IsSint32 a₁₄ →
  PIsHeap a₁₃ a i₂ →
  PMultisetUnchanged counts a₁₃ a₁₀ a zeroZ i₂ →
  PMultisetUnchanged counts a₁₃ a₁₀ a zeroZ x₁ →
  PLowerBound a₁₃ a i₂ x₁ a₁₄ →
  PUpperBound a₁₃ a zeroZ i₂ a₁₄

partial-sort-loop-inv-upper-preserved-goal9 : Set₁
partial-sort-loop-inv-upper-preserved-goal9 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal9 region linked counts
