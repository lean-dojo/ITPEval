-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/selection_sort/selection_sort_Why3_ide_VCselection_sort_loop_inv_reorder_preserved_goal3:
-- under the stated index bounds, integer ranges, memory validity, sortedness,
-- unchanged-range, minimum-element, and bound assumptions, the selection-sort
-- two-cell update preserves the array segment's multiset. This file contains
-- no proof.

{-# OPTIONS --safe #-}

module selection_sort_Why3_ide_VCselection_sort_loop_inv_reorder_preserved_goal3 where

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

zeroZ oneZ minusOneZ uint32Maximum uint32MaximumMinusOne : Int
zeroZ = pos zero
oneZ = pos (suc zero)
minusOneZ = negsuc zero
uint32Maximum = pos 4294967295
uint32MaximumMinusOne = pos 4294967294

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

PSorted :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PSorted integer-memory a lower upper =
  (left right : Int) →
  right <Z upper →
  lower ≤Z left →
  left <Z right →
  integer-memory (shift a left) ≤Z integer-memory (shift a right)

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

PStrictLowerBound :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PStrictLowerBound integer-memory a lower upper value =
  (index : Int) →
  lower ≤Z index →
  index <Z upper →
  value <Z integer-memory (shift a index)

PMinElement :
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Set
PMinElement integer-memory a upper minimum-index =
  (zeroZ ≤Z minimum-index) ∧
  (minimum-index <Z upper) ∧
  PLowerBound
    integer-memory
    a
    zeroZ
    upper
    (integer-memory (shift a minimum-index))

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

Goal3 :
  (Int → Int) →
  ((Int → Int) → Set) →
  CountOperations →
  Set
Goal3 region linked counts =
  (a : Addr) →
  (t₁ t₂ : Addr → Int) →
  (i₂ i₃ i₁ i : Int) →
  (allocation : Int → Int) →
  let
    a₁ = shift a zeroZ
    a₂ = havoc t₁ t₂ a₁ i₂
    a₃ = shift a i₃
    a₄ = shift a i₁
    a₅ = a₂ a₃
    a₆ = update (update a₂ a₃ i) a₄ a₅
    a₇ = a₆ a₃
    a₈ = a₂ a₄
    x₁ = subtractInt i₁ i₃
    x₂ = subtractInt i₂ i₃
    a₉ = a₂ (shift a (subtractInt i₃ oneZ))
  in
  a₇ ≡ a₈ →
  zeroZ ≤Z i₁ →
  i₁ <Z i₂ →
  i₃ ≤Z i₁ →
  i₁ ≤Z i₂ →
  i₃ ≤Z i₂ →
  zeroZ ≤Z i₃ →
  i₃ <Z i₂ →
  region (base a) ≤Z zeroZ →
  i₃ ≤Z uint32MaximumMinusOne →
  i₁ ≤Z uint32Maximum →
  i₂ ≤Z addInt uint32Maximum i₃ →
  linked allocation →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 i₃ →
  IsUint32 x₁ →
  IsSint32 (t₂ (shift a minusOneZ)) →
  ValidRW allocation a₁ i₂ →
  ValidRD allocation a₃ x₂ →
  IsSint32 a₈ →
  IsSint32 a₅ →
  IsSint32 a₉ →
  PSorted a₂ a zeroZ i₃ →
  IsSint32 a₇ →
  PMultisetUnchanged counts a₂ t₂ a zeroZ i₂ →
  PMinElement a₂ a₃ x₂ x₁ →
  PStrictLowerBound a₂ a₃ zeroZ x₁ a₈ →
  PUnchanged a₆ a₂ a zeroZ i₃ →
  PUnchanged a₆ a₂ a (addInt oneZ i₁) i₂ →
  PUnchanged a₆ a₂ a (addInt oneZ i₃) i₁ →
  (zeroZ <Z i₃ → PLowerBound a₂ a i₃ i₂ a₉) →
  PMultisetUnchanged counts a₆ t₂ a zeroZ i₂

selection-sort-loop-inv-reorder-preserved-goal3 : Set₁
selection-sort-loop-inv-reorder-preserved-goal3 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (counts : CountOperations) →
  Goal3 region linked counts
