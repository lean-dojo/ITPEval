-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_loop_inv_retain_preserved_goal16:
-- under the stated index, integer-range, heap, memory-validity, and multiset
-- assumptions, the next push-heap memory retains every signed-32 value other
-- than the displaced child value and the new parent-position value. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module push_heap_Why3_ide_VCpush_heap_loop_inv_retain_preserved_goal16 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; div-helper)

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

PMultisetAdd :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMultisetAdd counts current-memory previous-memory a upper value =
  addInt oneZ
    (lCount counts previous-memory a zeroZ upper value)
    ≡
  lCount counts current-memory a zeroZ upper value

PMultisetMinus :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMultisetMinus counts current-memory previous-memory a upper value =
  addInt oneZ
    (lCount counts current-memory a zeroZ upper value)
    ≡
  lCount counts previous-memory a zeroZ upper value

PMultisetRetain :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMultisetRetain counts current-memory previous-memory a upper value =
  lCount counts previous-memory a zeroZ upper value
    ≡
  lCount counts current-memory a zeroZ upper value

PMultisetRetainRest :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PMultisetRetainRest
  counts current-memory previous-memory a upper first-value second-value =
  (value : Int) →
  value ≠ first-value →
  value ≠ second-value →
  IsSint32 value →
  PMultisetRetain
    counts current-memory previous-memory a upper value

Goal16 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal16 conversion region linked counts =
  (i : Int) →
  (a : Addr) →
  (t₂ t₁ : Addr → Int) →
  (i₁ : Int) →
  (t₃ : Addr → Int) →
  (allocation : Int → Int) →
  let
    x = subtractInt i oneZ
    x₁ = heapParent x
    a₁ = shift a x₁
    x₂ = t₂ a₁
    a₂ = shift a x
    x₃ = t₂ a₂
    m = update t₂ a₂ x₂
    a₃ = shift a zeroZ
    a₄ = havoc t₁ m a₃ i
    a₅ = shift a i₁
    a₆ = a₄ a₅
    x₄ = heapParent i₁
    a₇ = shift a x₄
    a₈ = a₄ a₇
    x₅ = t₃ a₇
    a₉ = shift a (toUint32 conversion x)
  in
  zeroZ <Z i →
  zeroZ <Z i₁ →
  zeroZ ≤Z i₁ →
  region (base a) ≤Z zeroZ →
  zeroZ <Z x₁ →
  x₂ <Z x₃ →
  a₆ <Z x₃ →
  a₈ <Z x₃ →
  twoZ ≤Z i →
  addInt twoZ i₁ ≤Z i →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 x₄ →
  ValidRD allocation a₅ oneZ →
  ValidRW allocation a₃ i →
  IsUint32 x₁ →
  PIsHeap t₂ a x →
  IsSint32 x₅ →
  ValidRD allocation a₇ oneZ →
  IsUint32 (heapParent x₁) →
  IsSint32 x₃ →
  IsSint32 x₂ →
  ValidRD allocation a₉ oneZ →
  ValidRD allocation a₁ oneZ →
  ValidRW allocation a₉ oneZ →
  IsSint32 (m a₁) →
  IsSint32 a₆ →
  IsSint32 a₈ →
  PIsHeap a₄ a i →
  PMultisetMinus counts a₄ t₂ a i x₃ →
  PMultisetAdd counts a₄ t₂ a i a₆ →
  PMultisetRetainRest counts a₄ t₂ a i x₃ a₆ →
  ifSet
    (intLess a₆ a₈)
    ((update a₄ a₅ a₈ ≗ t₃) ∧
      ValidRW allocation a₅ oneZ)
    (a₄ ≗ t₃) →
  PMultisetRetainRest counts t₃ t₂ a i x₃ x₅

push-heap-loop-inv-retain-preserved-goal16 : Set₁
push-heap-loop-inv-retain-preserved-goal16 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal16 conversion region linked counts
