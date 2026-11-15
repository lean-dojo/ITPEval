-- Statement-only formalization of NTP4VC corpus artifact
-- pearl/queens_bv_Bits_belowqtvc: the 32-bit low-bits mask verification
-- condition relating a complemented left shift to the finite integer interval
-- containing exactly its set-bit indices. This file contains no proof.

{-# OPTIONS --safe #-}

module queens_bv_Bits_belowqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infix 2 _↔_

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

natEqual : Nat → Nat → Bool
natEqual zero zero = true
natEqual zero (suc _) = false
natEqual (suc _) zero = false
natEqual (suc m) (suc n) = natEqual m n

natLess : Nat → Nat → Bool
natLess zero zero = false
natLess zero (suc _) = true
natLess (suc _) zero = false
natLess (suc m) (suc n) = natLess m n

natLessOrEqual : Nat → Nat → Bool
natLessOrEqual zero _ = true
natLessOrEqual (suc _) zero = false
natLessOrEqual (suc m) (suc n) = natLessOrEqual m n

intEqual : Int → Int → Bool
intEqual (pos m) (pos n) = natEqual m n
intEqual (pos _) (negsuc _) = false
intEqual (negsuc _) (pos _) = false
intEqual (negsuc m) (negsuc n) = natEqual m n

intLess : Int → Int → Bool
intLess (pos m) (pos n) = natLess m n
intLess (pos _) (negsuc _) = false
intLess (negsuc _) (pos _) = true
intLess (negsuc m) (negsuc n) = natLess n m

intLessOrEqual : Int → Int → Bool
intLessOrEqual (pos m) (pos n) = natLessOrEqual m n
intLessOrEqual (pos _) (negsuc _) = false
intLessOrEqual (negsuc _) (pos _) = true
intLessOrEqual (negsuc m) (negsuc n) = natLessOrEqual n m

_≤Z_ : Int → Int → Set
x ≤Z y = intLessOrEqual x y ≡ true

_<Z_ : Int → Int → Set
x <Z y = intLess x y ≡ true

zeroZ thirtyTwoZ : Int
zeroZ = pos 0
thirtyTwoZ = pos 32

toNat : Int → Nat
toNat (pos n) = n
toNat (negsuc _) = zero

data Vec (A : Set) : Nat → Set where
  []V  : Vec A zero
  _∷V_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicate : {A : Set} → (n : Nat) → A → Vec A n
replicate zero value = []V
replicate (suc n) value = value ∷V replicate n value

nthVec : {A : Set} {n : Nat} → A → Nat → Vec A n → A
nthVec default index []V = default
nthVec default zero (x ∷V xs) = x
nthVec default (suc index) (_ ∷V xs) = nthVec default index xs

bitValue : Bool → Nat
bitValue false = zero
bitValue true = 1

unsignedNat : {n : Nat} → Vec Bool n → Nat
unsignedNat []V = zero
unsignedNat (bit ∷V bits) =
  bitValue bit + 2 * unsignedNat bits

unsignedZ : {n : Nat} → Vec Bool n → Int
unsignedZ bits = pos (unsignedNat bits)

half : Nat → Nat
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

lowBit : Nat → Bool
lowBit zero = false
lowBit (suc zero) = true
lowBit (suc (suc n)) = lowBit n

natToVec : (width value : Nat) → Vec Bool width
natToVec zero value = []V
natToVec (suc width) value =
  lowBit value ∷V natToVec width (half value)

prefix : {A : Set} {n : Nat} → Vec A (suc n) → Vec A n
prefix {n = zero} (_ ∷V []V) = []V
prefix {n = suc n} (x ∷V xs) = x ∷V prefix xs

shiftLeftOnce :
  {n : Nat} →
  Vec Bool (suc n) →
  Vec Bool (suc n)
shiftLeftOnce bits = false ∷V prefix bits

shiftLeftNat :
  {n : Nat} →
  Vec Bool (suc n) →
  Nat →
  Vec Bool (suc n)
shiftLeftNat bits zero = bits
shiftLeftNat bits (suc amount) =
  shiftLeftNat (shiftLeftOnce bits) amount

notBit : Bool → Bool
notBit false = true
notBit true = false

notVec : {n : Nat} → Vec Bool n → Vec Bool n
notVec []V = []V
notVec (bit ∷V bits) = notBit bit ∷V notVec bits

Word32 : Set
Word32 = Vec Bool 32

allOnes32 thirtyTwoWord : Word32
allOnes32 = replicate 32 true
thirtyTwoWord = natToVec 32 32

wordLe : Word32 → Word32 → Set
wordLe left right =
  natLessOrEqual (unsignedNat left) (unsignedNat right) ≡ true

bitAt : Word32 → Int → Bool
bitAt bits index = nthVec false (toNat index) bits

belowMask : Word32 → Word32
belowMask n =
  notVec (shiftLeftNat allOnes32 (unsignedNat n))

contains : Int → List Int → Bool
contains sought [] = false
contains sought (x ∷ xs) with intEqual sought x
... | true = true
... | false = contains sought xs

record FSet : Set where
  constructor fset
  field
    elements : List Int

open FSet

member : Int → FSet → Set
member index set = contains index (elements set) ≡ true

subset : FSet → FSet → Set
subset left right =
  (index : Int) → member index left → member index right

setEqual : FSet → FSet → Set
setEqual left right =
  subset left right ∧ subset right left

rangeBelow : Nat → List Int
rangeBelow zero = []
rangeBelow (suc n) = pos n ∷ rangeBelow n

intervalFromZero : Nat → FSet
intervalFromZero upper = fset (rangeBelow upper)

record BitsContext : Set₁ where
  field
    T          : Set
    inhabitant : T
    bv         : T → Word32
    mdl        : T → FSet

    t-invariant :
      (i : Int) →
      (self : T) →
      (((zeroZ ≤Z i ∧ i <Z thirtyTwoZ) ∧
        bitAt (bv self) i ≡ true) ↔
       member i (mdl self))

    t-injective :
      (left right : T) →
      (bv left ≡ bv right ∧ setEqual (mdl left) (mdl right)) →
      left ≡ right

open BitsContext

BelowVC : BitsContext → Word32 → Set
BelowVC context n =
  wordLe n thirtyTwoWord →
  let
    o1 = intervalFromZero (unsignedNat n)
    o2 = belowMask n
  in
  ((i : Int) →
    (((zeroZ ≤Z i ∧ i <Z thirtyTwoZ) ∧
      bitAt o2 i ≡ true) ↔
     member i o1))
  ∧
  ((result : T context) →
    (bv context result ≡ o2 ∧
     setEqual (mdl context result) o1) →
    setEqual
      (mdl context result)
      (intervalFromZero (unsignedNat n)))

queens-bv-Bits-belowqtvc : Set₁
queens-bv-Bits-belowqtvc =
  (context : BitsContext) →
  (n : Word32) →
  BelowVC context n
