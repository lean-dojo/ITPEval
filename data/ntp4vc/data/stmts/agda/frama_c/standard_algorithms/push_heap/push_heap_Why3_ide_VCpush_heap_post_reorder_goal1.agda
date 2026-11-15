-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/push_heap/push_heap_Why3_ide_VCpush_heap_post_reorder_goal1:
-- under the stated integer bounds, memory-validity, heap, conditional reorder,
-- havoc-update, and multiset assumptions, the reordered heap prefix has the
-- same multiplicity for every signed-32 value. This file contains no proof.

{-# OPTIONS --safe #-}

module push_heap_Why3_ide_VCpush_heap_post_reorder_goal1 where

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

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

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

PMultisetUnchanged :
  CountOperations →
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMultisetUnchanged
  counts current-memory previous-memory a lower upper =
  (value : Int) →
  IsSint32 value →
  lCount counts previous-memory a lower upper value
    ≡
  lCount counts current-memory a lower upper value

Goal1 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal1 conversion region linked counts =
  (a : Addr) →
  (i₁ : Int) →
  (i₅ : Int) →
  (t₄ : Addr → Int) →
  (i₃ : Int) →
  (t₂ : Addr → Int) →
  (i : Int) →
  (allocation : Int → Int) →
  (i₂ : Int) →
  (i₄ : Int) →
  (p₁ : Bool) →
  (t₃ : Addr → Int) →
  (p : Bool) →
  (t₁ : Addr → Int) →
  let
    a₁ = shift a zeroZ
    x = subtractInt i₁ oneZ
    a₂ = shift a i₅
    a₃ = shift a (toUint32 conversion x)
    x₁ = t₄ a₂
    a₄ = shift a x
    x₂ = t₄ a₄
    a₅ = shift a i₃
    m = update t₄ a₄ x₁
    x₃ = t₂ a₅
    a₆ = shift a i
  in
  zeroZ <Z i₁ →
  region (base a) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsUint32 i₄ →
  IsUint32 i₅ →
  ValidRW allocation a₁ i₁ →
  PIsHeap t₄ a x →
  ifSet
    (intLessOrEqual twoZ i₁)
    ((p₁ ≡ false) ∧
      (heapParent x ≡ i₅) ∧
      ValidRD allocation a₂ oneZ ∧
      ValidRD allocation a₃ oneZ ∧
      ifSet
        (intLess x₁ x₂)
        ((update t₂ a₅ x₂ ≗ t₃) ∧
          ValidRW allocation a₅ oneZ ∧
          ValidRW allocation a₃ oneZ ∧
          ifSet
            (intLess zeroZ i₅)
            ((p ≡ false) ∧
              (i₃ ≡ i₂) ∧
              (i₄ ≡ i₂) ∧
              (i₄ ≡ i₃) ∧
              (heapParent i₃ ≡ i) ∧
              (havoc t₁ m a₁ i₁ ≗ t₂) ∧
              (zeroZ ≤Z i₃) ∧
              (x₃ <Z x₂) ∧
              (addInt twoZ i₃ ≤Z i₁) ∧
              PIsHeap t₂ a i₁ ∧
              PMultisetAdd counts t₂ t₄ a i₁ x₃ ∧
              PMultisetMinus counts t₂ t₄ a i₁ x₂ ∧
              PMultisetRetainRest counts t₂ t₄ a i₁ x₂ x₃ ∧
              Either
                (i₃ ≤Z zeroZ)
                ((x₂ ≤Z t₂ a₆) ∧
                  ValidRD allocation a₆ oneZ))
            ((i₅ ≡ i₃) ∧ (m ≗ t₂)))
        (t₄ ≗ t₃))
    (t₄ ≗ t₃) →
  PMultisetUnchanged counts t₃ t₄ a zeroZ i₁

push-heap-post-reorder-goal1 : Set₁
push-heap-post-reorder-goal1 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal1 conversion region linked counts
