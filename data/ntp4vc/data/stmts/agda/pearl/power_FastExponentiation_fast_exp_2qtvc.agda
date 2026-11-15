-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/power_FastExponentiation_fast_exp_2qtvc: the fast-exponentiation
-- verification condition for recursive-call descent and accumulator
-- correctness over nonnegative integer exponents. This file contains no proof.

{-# OPTIONS --safe #-}

module power_FastExponentiation_fast_exp_2qtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _-_; _*_; div-helper)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_

data ⊥ : Set where

Not : Set → Set
Not A = A → ⊥

_≠_ : {A : Set} → A → A → Set
x ≠ y = Not (x ≡ y)

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

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

differenceNat : Nat → Nat → Int
differenceNat zero zero = pos zero
differenceNat (suc m) zero = pos (suc m)
differenceNat zero (suc n) = negsuc n
differenceNat (suc m) (suc n) = differenceNat m n

addInt : Int → Int → Int
addInt (pos m) (pos n) = pos (m + n)
addInt (pos m) (negsuc n) = differenceNat m (suc n)
addInt (negsuc m) (pos n) = differenceNat n (suc m)
addInt (negsuc m) (negsuc n) = negsuc (suc (m + n))

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negative (m * suc n)
multiplyInt (negsuc m) (pos n) =
  negative (suc m * n)
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

powerNat : Int → Nat → Int
powerNat base zero = pos 1
powerNat base (suc exponent) =
  multiplyInt base (powerNat base exponent)

powerInt : Int → Int → Int
powerInt base exponent =
  powerNat base (intToNat exponent)

natDivide : Nat → Nat → Nat
natDivide n zero = zero
natDivide n (suc m) = div-helper zero m n m

natModulo : Nat → Nat → Nat
natModulo n zero = zero
natModulo n d@(suc _) = n - d * natDivide n d

tdivInt : Int → Int → Int
tdivInt (pos _) (pos zero) = pos zero
tdivInt (pos n) (pos (suc m)) =
  pos (natDivide n (suc m))
tdivInt (pos n) (negsuc m) =
  negative (natDivide n (suc m))
tdivInt (negsuc _) (pos zero) = pos zero
tdivInt (negsuc n) (pos (suc m)) =
  negative (natDivide (suc n) (suc m))
tdivInt (negsuc n) (negsuc m) =
  pos (natDivide (suc n) (suc m))

tmodInt : Int → Int → Int
tmodInt (pos n) divisor =
  pos (natModulo n (absoluteNat divisor))
tmodInt (negsuc n) divisor =
  negative (natModulo (suc n) (absoluteNat divisor))

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos 1
twoZ = pos 2

DescentVC : Int → Set
DescentVC n =
  Not (n ≡ zeroZ) →
  twoZ ≠ zeroZ
  ∧ IfSet
      (intEqual (tmodInt n twoZ) zeroZ)
      (twoZ ≠ zeroZ
       ∧
       let o1 = tdivInt n twoZ
       in
       (zeroZ ≤Z n ∧ o1 <Z n)
       ∧ zeroZ ≤Z o1)
      (let o1 = subtractInt n oneZ
       in
       (zeroZ ≤Z n ∧ o1 <Z n)
       ∧ zeroZ ≤Z o1)

ResultPremise : Int → Int → Int → Int → Set
ResultPremise n acc x result =
  IfSet
    (intEqual n zeroZ)
    (result ≡ acc)
    (IfSet
      (intEqual (tmodInt n twoZ) zeroZ)
      (result ≡
       multiplyInt
         (powerInt
           (multiplyInt x x)
           (tdivInt n twoZ))
         acc)
      (result ≡
       multiplyInt
         (powerInt x (subtractInt n oneZ))
         (multiplyInt x acc)))

fast-exp-2-vc : Set
fast-exp-2-vc =
  (n acc x : Int) →
  zeroZ ≤Z n →
  DescentVC n
  ∧
  ((result : Int) →
    ResultPremise n acc x result →
    result ≡ multiplyInt (powerInt x n) acc)
