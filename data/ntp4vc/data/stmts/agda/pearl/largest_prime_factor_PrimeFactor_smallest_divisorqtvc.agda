-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/largest_prime_factor_PrimeFactor_smallest_divisorqtvc: the
-- smallest-divisor verification condition, including recursive-call progress
-- and the minimal-divisor specification for every possible result. This file
-- contains no proof.

{-# OPTIONS --safe #-}

module largest_prime_factor_PrimeFactor_smallest_divisorqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat
  using (Nat; zero; suc; _+_; _*_)

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

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

IfBool : Bool → Bool → Bool → Bool
IfBool true when-true when-false = when-true
IfBool false when-true when-false = when-false

boolEqual : Bool → Bool → Bool
boolEqual true true = true
boolEqual true false = false
boolEqual false true = false
boolEqual false false = true

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

natSubtract : Nat → Nat → Nat
natSubtract m zero = m
natSubtract zero (suc _) = zero
natSubtract (suc m) (suc n) = natSubtract m n

IfNat : Bool → Nat → Nat → Nat
IfNat true when-true when-false = when-true
IfNat false when-true when-false = when-false

natModFuel : Nat → Nat → Nat → Nat
natModFuel zero dividend divisor = dividend
natModFuel (suc fuel) dividend zero = dividend
natModFuel (suc fuel) dividend (suc divisor) =
  IfNat
    (natLess dividend (suc divisor))
    dividend
    (natModFuel
      fuel
      (natSubtract dividend (suc divisor))
      (suc divisor))

natMod : Nat → Nat → Nat
natMod dividend divisor =
  natModFuel (suc dividend) dividend divisor

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
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

absoluteNat : Int → Nat
absoluteNat (pos n) = n
absoluteNat (negsuc n) = suc n

-- Signed remainder with the dividend's sign. On the VC's positive n and d,
-- this is Why3's integer remainder used by the source expression n % d.
tmodInt : Int → Int → Int
tmodInt (pos n) divisor =
  pos (natMod n (absoluteNat divisor))
tmodInt (negsuc n) divisor =
  negative (natMod (suc n) (absoluteNat divisor))

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

Divides : Int → Int → Set
Divides divisor dividend =
  Exists Int λ quotient →
    dividend ≡ multiplyInt divisor quotient

NoSmallerDivisor : Int → Int → Set
NoSmallerDivisor n upper =
  (i : Int) →
  twoZ ≤Z i ∧ i <Z upper →
  Not (Divides i n)

DivisibilityTestEquation : Int → Int → Bool → Set
DivisibilityTestEquation n d o2 =
  IfSet
    (intLessOrEqual twoZ d)
    (o2 ≡
      IfBool
        (intEqual (tmodInt n d) zeroZ)
        true
        false)
    (o2 ≡ false)

NextDivisorVC : Int → Int → Set
NextDivisorVC n d =
  let o3 = addInt d oneZ
  in
  (zeroZ ≤Z subtractInt n d
   ∧ subtractInt n o3 <Z subtractInt n d)
  ∧ twoZ ≤Z n
  ∧ (twoZ ≤Z o3 ∧ o3 ≤Z n)
  ∧ NoSmallerDivisor n o3

ProgressVC : Int → Int → Set
ProgressVC n d =
  let o1 = multiplyInt d d
  in
  Not (n <Z o1) →
  (twoZ ≤Z d → d ≠ zeroZ)
  ∧
  ((o2 : Bool) →
    DivisibilityTestEquation n d o2 →
    o2 ≠ true →
    NextDivisorVC n d)

ResultPremise : Int → Int → Int → Set
ResultPremise n d result =
  let o1 = multiplyInt d d
  in
  IfSet
    (intLess n o1)
    (result ≡ n)
    (Exists Bool λ o2 →
      DivisibilityTestEquation n d o2
      ∧
      IfSet
        (boolEqual o2 true)
        (result ≡ d)
        ((addInt d oneZ ≤Z result ∧ result ≤Z n)
         ∧ Divides result n
         ∧ NoSmallerDivisor n result))

ResultSpecification : Int → Int → Int → Set
ResultSpecification n d result =
  (d ≤Z result ∧ result ≤Z n)
  ∧ Divides result n
  ∧ NoSmallerDivisor n result

smallest-divisor-vc : Set
smallest-divisor-vc =
  (n d : Int) →
  twoZ ≤Z n →
  twoZ ≤Z d →
  d ≤Z n →
  NoSmallerDivisor n d →
  ProgressVC n d
  ∧
  ((result : Int) →
    ResultPremise n d result →
    ResultSpecification n d result)
