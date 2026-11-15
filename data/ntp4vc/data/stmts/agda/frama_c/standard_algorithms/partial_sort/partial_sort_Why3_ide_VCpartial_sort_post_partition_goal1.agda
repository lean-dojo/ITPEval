-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/partial_sort/partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1:
-- under the stated index, region, linkedness, integer-range, memory-validity,
-- heap, multiset, unchanged-range, sortedness, and bound assumptions, the
-- final memory satisfies the partial-sort partition property.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module partial_sort_Why3_ide_VCpartial_sort_post_partition_goal1 where

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

IfSet : Bool → Set → Set → Set
IfSet true when-true _ = when-true
IfSet false _ when-false = when-false

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

zeroZ oneZ twoZ uint32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
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

FunctionEqual :
  {A B : Set} →
  (A → B) →
  (A → B) →
  Set
FunctionEqual {A = A} left right =
  (argument : A) →
  left argument ≡ right argument

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

PSorted :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PSorted integer-memory a lower upper =
  (earlier later : Int) →
  later <Z upper →
  lower ≤Z earlier →
  earlier <Z later →
  integer-memory (shift a earlier)
    ≤Z
  integer-memory (shift a later)

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

PPartition :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PPartition integer-memory a split upper =
  zeroZ ≤Z split →
  split ≤Z upper →
  (left-index right-index : Int) →
  split ≤Z right-index →
  right-index <Z upper →
  zeroZ ≤Z left-index →
  left-index <Z split →
  integer-memory (shift a left-index)
    ≤Z
  integer-memory (shift a right-index)

Goal1 :
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal1 region linked counts =
  (a : Addr) →
  (t₆ t₃ t₅ : Addr → Int) →
  (i₂ i₁ i : Int) →
  (t : Int → Int) →
  (p : Bool) →
  (t₁ : Int → Int) →
  (t₂ t₈ t₄ t₇ : Addr → Int) →
  let
    a₁ = shift a zeroZ
    x = t₆ a₁
    a₂ = havoc t₃ t₅ a₁ i₂
  in
  i₁ ≤Z i →
  zeroZ ≤Z i₁ →
  region (base a) ≤Z zeroZ →
  linked t →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsSint32 (t₅ a₁) →
  IsSint32 x →
  ValidRW t a₁ i →
  IfSet
    (intLess zeroZ i₁)
    ((p ≡ false) ∧
     FunctionEqual t₁ t ∧
     FunctionEqual (havoc t₂ t₈ a₁ i₁) t₅ ∧
     FunctionEqual (havoc t₃ t₅ a₁ i) t₆ ∧
     FunctionEqual (havoc t₄ a₂ a₁ i₁) t₇ ∧
     (i₂ ≤Z i) ∧
     (i ≤Z i₂) ∧
     (i₁ ≤Z i₂) ∧
     PSorted t₇ a zeroZ i₁ ∧
     PIsHeap t₅ a i₁ ∧
     PIsHeap t₆ a i₁ ∧
     PMultisetUnchanged counts t₅ t₈ a zeroZ i₁ ∧
     PMultisetUnchanged counts t₆ t₈ a zeroZ i₂ ∧
     PUnchanged t₆ t₈ a i₂ i ∧
     ValidRW t₁ a₁ i₁ ∧
     PUpperBound t₆ a zeroZ i₁ x ∧
     PLowerBound t₆ a i₁ i₂ x ∧
     PMultisetUnchanged counts t₇ a₂ a zeroZ i₁)
    (FunctionEqual t₈ t₇) →
  PPartition t₇ a i₁ i

partial-sort-post-partition-goal1 : Set₁
partial-sort-post-partition-goal1 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal1 region linked counts
