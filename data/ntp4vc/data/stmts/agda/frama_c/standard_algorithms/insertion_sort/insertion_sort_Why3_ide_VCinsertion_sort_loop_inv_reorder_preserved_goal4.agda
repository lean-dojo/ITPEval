-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/standard_algorithms/insertion_sort/insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_reorder_preserved_goal4:
-- under the stated integer bounds, memory-validity, sortedness, unchanged-range,
-- multiset, and bound assumptions, shifting the insertion-sort range preserves
-- its multiset. This file contains no proof.

{-# OPTIONS --safe #-}

module insertion_sort_Why3_ide_VCinsertion_sort_loop_inv_reorder_preserved_goal4 where

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

zeroZ oneZ uint32Maximum uint32Upper signed32Lower signed32Upper : Int
zeroZ = pos zero
oneZ = pos (suc zero)
uint32Maximum = pos 4294967295
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

record Uint32Conversion : Set where
  field
    toUint32 : Int → Int

    resultInRange :
      (x : Int) →
      IsUint32 (toUint32 x)

    identityInRange :
      (x : Int) →
      IsUint32 x →
      toUint32 x ≡ x

open Uint32Conversion

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

PEqualRanges :
  (Addr → Int) →
  (Addr → Int) →
  Addr →
  Int →
  Int →
  Int →
  Set
PEqualRanges current-memory previous-memory a lower upper previous-lower =
  (index : Int) →
  zeroZ ≤Z index →
  index <Z subtractInt upper lower →
  previous-memory (shift (shift a lower) index)
    ≡
  current-memory (shift (shift a previous-lower) index)

Goal4 :
  (Int → Int) →
  ((Int → Int) → Set) →
  Uint32Conversion →
  CountOperations →
  Set
Goal4 region linked conversion counts =
  (i₂ i₁ : Int) →
  (a : Addr) →
  (t₁ t₃ : Addr → Int) →
  (i : Int) →
  (t₂ : Addr → Int) →
  (allocation : Int → Int) →
  let
    x₁ = subtractInt i₂ i₁
    x₂ = addInt oneZ i₂
    a₁ = shift a zeroZ
    a₂ = shift a i₂
    a₃ = shift a i₁
    x₃ = subtractInt (addInt oneZ i₂) i₁
    a₄ = havoc t₁ t₃ a₁ i
    a₅ = a₄ a₂
    a₆ = havoc t₂ a₄ a₃ x₃
  in
  i₂ ≤Z i →
  zeroZ ≤Z i₁ →
  zeroZ ≤Z i₂ →
  i₂ <Z i →
  i₁ ≤Z i₂ →
  region (base a) ≤Z zeroZ →
  i₂ ≤Z pos 4294967294 →
  i₂ ≤Z addInt uint32Maximum i₁ →
  toUint32 conversion x₁ ≤Z pos 4294967294 →
  linked allocation →
  IsUint32 i →
  IsUint32 i₁ →
  IsUint32 i₂ →
  IsUint32 x₂ →
  ValidRD allocation a₁ i₂ →
  ValidRD allocation a₂ oneZ →
  ValidRW allocation a₁ i →
  ValidRW allocation a₃ x₃ →
  IsSint32 a₅ →
  PSorted a₄ a zeroZ i₂ →
  PUnchanged a₄ t₃ a i₂ i →
  PMultisetUnchanged counts a₄ t₃ a zeroZ i₂ →
  PUpperBound a₄ a zeroZ i₁ a₅ →
  PStrictLowerBound a₄ a i₁ i₂ a₅ →
  PEqualRanges a₆ a₄ a₃ zeroZ x₁ oneZ →
  PEqualRanges a₆ a₄ a₃ x₁ x₃ zeroZ →
  PMultisetUnchanged counts a₆ t₃ a zeroZ x₂

insertion-sort-loop-inv-reorder-preserved-goal4 : Set₁
insertion-sort-loop-inv-reorder-preserved-goal4 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (conversion : Uint32Conversion) →
  (counts : CountOperations) →
  Goal4 region linked conversion counts
