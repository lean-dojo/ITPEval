-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/pop_heap/pop_heap_Why3_ide_VCpop_heap_post_result_goal1:
-- under the stated heap, maximum-child, integer-range, memory-validity,
-- memory-update, parent-index, upper-bound, and value-count assumptions, the
-- value stored at the final heap position equals the original root value.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module pop_heap_Why3_ide_VCpop_heap_post_result_goal1 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using
  (Nat; zero; suc; _+_; _*_; div-helper)

infix 4 _≠_ _≗_ _≤Z_ _<Z_
infixr 3 _∧_

data Bottom : Set where

Not : Set → Set
Not proposition = proposition → Bottom

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

_≗_ : {A B : Set} → (A → B) → (A → B) → Set
_≗_ {A = A} f g = (x : A) → f x ≡ g x

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) = negative (m * suc n)
multiplyInt (negsuc m) (pos n) = negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) = pos (suc m * suc n)

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

addrEqual : Addr → Addr → Bool
addrEqual p q =
  ifValue
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))
    false

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifValue (addrEqual query location) value (memory query)

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false value = value

notBool : Bool → Bool
notBool true = false
notBool false = true

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
havoc old-memory new-memory start length query =
  ifValue
    (separatedBool query oneZ start length)
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

heapParent : Int → Int
heapParent index =
  truncateDivide (subtractInt index oneZ) twoZ

heapLeft : Int → Int
heapLeft index =
  addInt oneZ (multiplyInt twoZ index)

heapRight : Int → Int
heapRight index =
  addInt twoZ (multiplyInt twoZ index)

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
    child-value = integer-memory (shift a child)
    right = heapRight parent
  in
  (zeroZ ≤Z parent) ∧
  (addInt twoZ parent ≤Z upper) ∧
  (parent ≤Z parentIndexUpper →
    heapParent child ≡ parent) ∧
  (addInt twoZ left ≤Z upper →
    integer-memory (shift a left) ≤Z child-value) ∧
  (addInt twoZ right ≤Z upper →
    integer-memory (shift a right) ≤Z child-value)

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

Goal1 :
  Uint32Projection →
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal1 conversion region linked counts =
  (a : Addr) →
  (t₅ : Addr → Int) →
  (i : Int) →
  (t₄ : Addr → Int) →
  (i₁ : Int) →
  (t₃ : Addr → Int) →
  (i₃ : Int) →
  (allocation : Int → Int) →
  (i₂ : Int) →
  (p p₁ : Bool) →
  (allocation₁ : Int → Int) →
  (t₂ : Addr → Int) →
  let
    a₁ = shift a zeroZ
    x = t₅ a₁
    x₁ = subtractInt i oneZ
    a₂ = shift a x₁
    x₂ = t₄ a₂
    a₃ = shift a (toUint32 conversion x₁)
    a₄ = shift a i₁
    x₃ = t₃ a₂
    a₅ = shift a i₃
  in
  zeroZ <Z i →
  region (base a) ≤Z zeroZ →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  PIsHeap t₅ a i →
  IsSint32 x →
  ValidRW allocation a₁ i →
  IsSint32 x₂ →
  ifSet
    (intLessOrEqual twoZ i)
    (ValidRD allocation a₁ oneZ ∧
      ValidRD allocation a₃ oneZ ∧
      ifSet
        (intLess (t₅ a₂) x)
        (p ≡ false ∧
          p₁ ≡ false ∧
          allocation₁ ≗ allocation ∧
          havoc t₂ t₅ a₁ x₁ ≗ t₃ ∧
          update (update t₃ a₄ x₃) a₂ x ≗ t₄ ∧
          zeroZ <Z i₂ ∧
          zeroZ ≤Z i₁ ∧
          i₁ <Z i₃ ∧
          x₃ <Z t₃ (shift a (heapParent i₁)) ∧
          addInt twoZ i₁ ≤Z i ∧
          PIsHeap t₃ a i ∧
          PHeapMaximumChild t₃ a i i₁ i₃ ∧
          PHeapMaximumChild t₅ a i zeroZ i₂ ∧
          ValidRW allocation₁ a₁ i ∧
          ValidRW allocation₁ a₄ oneZ ∧
          PUpperBound t₃ a zeroZ i x ∧
          ValidRD allocation₁ a₃ oneZ ∧
          ValidRW allocation₁ a₃ oneZ ∧
          (addInt twoZ i₂ ≤Z i →
            heapParent i₂ ≡ zeroZ) ∧
          (addInt twoZ i₃ ≤Z i →
            heapParent i₃ ≡ i₁) ∧
          Either
            (i ≤Z addInt oneZ i₃)
            ((t₃ a₅ ≤Z x₃) ∧
              ValidRD allocation₁ a₅ oneZ) ∧
          ((value : Int) →
            IsSint32 value →
            addInt
              (lCount counts t₅ a zeroZ i value)
              (ifValue (intEqual (t₃ a₄) value) oneZ zeroZ)
              ≡
            addInt
              (lCount counts t₃ a zeroZ i value)
              (ifValue (intEqual x value) oneZ zeroZ)))
        (t₅ ≗ t₄))
    (t₅ ≗ t₄) →
  x₂ ≡ x

pop-heap-post-result-goal1 : Set₁
pop-heap-post-result-goal1 =
  (conversion : Uint32Projection) →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal1 conversion region linked counts
