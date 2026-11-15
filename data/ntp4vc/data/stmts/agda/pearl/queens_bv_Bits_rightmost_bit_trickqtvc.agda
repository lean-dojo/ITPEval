-- Statement-only formalization of NTP4VC corpus artifact
-- pearl/queens_bv_Bits_rightmost_bit_trickqtvc: the 32-bit rightmost-set-bit
-- verification condition relating x AND its two's-complement negation to the
-- singleton containing the least set-bit index. This file contains no proof.

{-# OPTIONS --safe #-}

module queens_bv_Bits_rightmost_bit_trickqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≤Z_ _<Z_
infixr 5 _∷V_
infixr 3 _∧_
infix 2 _↔_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

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

notBit : Bool → Bool
notBit false = true
notBit true = false

andBit : Bool → Bool → Bool
andBit false _ = false
andBit true y = y

orBit : Bool → Bool → Bool
orBit false y = y
orBit true _ = true

xorBit : Bool → Bool → Bool
xorBit false y = y
xorBit true false = true
xorBit true true = false

andVec : {n : Nat} → Vec Bool n → Vec Bool n → Vec Bool n
andVec []V []V = []V
andVec (x ∷V xs) (y ∷V ys) =
  andBit x y ∷V andVec xs ys

differenceBit : Bool → Bool → Bool → Bool
differenceBit borrow x y = xorBit (xorBit x y) borrow

borrowBit : Bool → Bool → Bool → Bool
borrowBit borrow x y =
  orBit
    (andBit (notBit x) y)
    (andBit borrow (notBit (xorBit x y)))

subtractWithBorrow :
  {n : Nat} →
  Bool →
  Vec Bool n →
  Vec Bool n →
  Vec Bool n
subtractWithBorrow borrow []V []V = []V
subtractWithBorrow borrow (x ∷V xs) (y ∷V ys) =
  differenceBit borrow x y ∷V
  subtractWithBorrow (borrowBit borrow x y) xs ys

Word32 : Set
Word32 = Vec Bool 32

zeroWord32 : Word32
zeroWord32 = replicate 32 false

wordNegate : Word32 → Word32
wordNegate bits =
  subtractWithBorrow false zeroWord32 bits

rightmostBit : Word32 → Word32
rightmostBit bits =
  andVec bits (wordNegate bits)

bitAt : Word32 → Int → Bool
bitAt bits index = nthVec false (toNat index) bits

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

emptySet : FSet
emptySet = fset []

singleton : Int → FSet
singleton value = fset (value ∷ [])

minimumFrom : Int → List Int → Int
minimumFrom current [] = current
minimumFrom current (x ∷ xs) with intLess x current
... | true = minimumFrom x xs
... | false = minimumFrom current xs

minimum : FSet → Int
minimum (fset []) = zeroZ
minimum (fset (x ∷ xs)) = minimumFrom x xs

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

RightmostBitVC : BitsContext → Set
RightmostBitVC context =
  (a : T context) →
  Not (setEqual (mdl context a) emptySet) →
  let
    res = rightmostBit (bv context a)
    least = minimum (mdl context a)
    o1 = singleton least
  in
  ((i : Int) →
    (((zeroZ ≤Z i ∧ i <Z thirtyTwoZ) ∧
      bitAt res i ≡ true) ↔
     member i o1))
  ∧
  ((result : T context) →
    (bv context result ≡ res ∧
     setEqual (mdl context result) o1) →
    setEqual
      (mdl context result)
      (singleton least))

queens-bv-Bits-rightmost-bit-trickqtvc : Set₁
queens-bv-Bits-rightmost-bit-trickqtvc =
  (context : BitsContext) →
  RightmostBitVC context
