-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_loop_inv_max_established_goal9:
-- under the stated heap, maximum-child, integer-range, memory-validity, and
-- parent-index assumptions, the root value is an upper bound for the heap
-- prefix. This file contains no proof.

{-# OPTIONS --safe #-}

module pop_heap_Why3_ide_VCpop_heap_loop_inv_max_established_goal9 where

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

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

uint32Upper parentIndexUpper signed32Lower signed32Upper : Int
uint32Upper = pos 4294967296
parentIndexUpper = pos 2147483646
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

heapParent : Int → Int
heapParent index =
  truncateDivide (subtractInt index oneZ) twoZ

heapLeft : Int → Int
heapLeft index =
  addInt oneZ (addInt index index)

heapRight : Int → Int
heapRight index =
  addInt twoZ (addInt index index)

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

PHeapMaximumChild :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PHeapMaximumChild integer-memory a upper parent child =
  let
    left = heapLeft parent
    childValue = integer-memory (shift a child)
    right = heapRight parent
  in
  (zeroZ ≤Z parent) ∧
  (addInt twoZ parent ≤Z upper) ∧
  (parent ≤Z parentIndexUpper →
    heapParent child ≡ parent) ∧
  (addInt twoZ left ≤Z upper →
    integer-memory (shift a left) ≤Z childValue) ∧
  (addInt twoZ right ≤Z upper →
    integer-memory (shift a right) ≤Z childValue)

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

Goal9 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  Set
Goal9 conversion region linked =
  (i : Int) →
  (integer-memory : Addr → Int) →
  (a : Addr) →
  (i₁ : Int) →
  (allocation : Int → Int) →
  let
    x = subtractInt i oneZ
    x₁ = integer-memory (shift a x)
    a₁ = shift a zeroZ
    x₂ = integer-memory a₁
  in
  zeroZ <Z i →
  zeroZ <Z i₁ →
  region (base a) ≤Z zeroZ →
  x₁ <Z x₂ →
  twoZ ≤Z i →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  PIsHeap integer-memory a i →
  IsSint32 x₂ →
  PHeapMaximumChild integer-memory a i zeroZ i₁ →
  ValidRD allocation a₁ oneZ →
  ValidRW allocation a₁ i →
  IsSint32 (integer-memory (shift a (heapParent zeroZ))) →
  IsSint32 x₁ →
  ValidRD
    allocation
    (shift a (toUint32 conversion x))
    oneZ →
  (addInt twoZ i₁ ≤Z i →
    heapParent i₁ ≡ zeroZ) →
  PUpperBound integer-memory a zeroZ i x₂

pop-heap-loop-inv-max-established-goal9 : Set₁
pop-heap-loop-inv-max-established-goal9 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  Goal9 conversion region linked
