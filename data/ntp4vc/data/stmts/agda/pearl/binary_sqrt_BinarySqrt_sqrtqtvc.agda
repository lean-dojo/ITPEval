-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/binary_sqrt_BinarySqrt_sqrtqtvc: the binary-square-root verification
-- condition for the doubling invariant and the final one-step square-root
-- approximation bound. This file contains no proof.

{-# OPTIONS --safe #-}

module binary_sqrt_BinarySqrt_sqrtqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infix 4 _≠_ _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

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

data _∨_ (A B : Set) : Set where
  left  : A → A ∨ B
  right : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

Conditional : Set → Set → Set → Set
Conditional condition when-true when-false =
  (condition ∧ when-true) ∨ (Not condition ∧ when-false)

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

multiplyInt : Int → Int → Int
multiplyInt (pos m) (pos n) = pos (m * n)
multiplyInt (pos m) (negsuc n) =
  negateInt (pos (m * suc n))
multiplyInt (negsuc m) (pos n) =
  negateInt (pos (suc m * n))
multiplyInt (negsuc m) (negsuc n) =
  pos (suc m * suc n)

subtractInt : Int → Int → Int
subtractInt x y = addInt x (negateInt y)

oneN twoN : Nat
oneN = suc zero
twoN = suc oneN

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos oneN
twoZ = pos twoN

record StandardReal (R : Set) : Set₁ where
  field
    zeroR oneR : R
    add multiply : R → R → R
    negate reciprocal : R → R
    lessOrEqual : R → R → Set
    fromNat : Nat → R

    one-not-zero :
      oneR ≠ zeroR

    add-commutative :
      (x y : R) → add x y ≡ add y x
    add-associative :
      (x y z : R) → add (add x y) z ≡ add x (add y z)
    add-zero :
      (x : R) → add x zeroR ≡ x
    add-inverse :
      (x : R) → add x (negate x) ≡ zeroR

    multiply-commutative :
      (x y : R) → multiply x y ≡ multiply y x
    multiply-associative :
      (x y z : R) →
      multiply (multiply x y) z ≡ multiply x (multiply y z)
    multiply-one :
      (x : R) → multiply x oneR ≡ x
    multiply-zero :
      (x : R) → multiply x zeroR ≡ zeroR
    distribute :
      (x y z : R) →
      multiply x (add y z) ≡
      add (multiply x y) (multiply x z)
    reciprocal-zero :
      reciprocal zeroR ≡ zeroR
    multiply-reciprocal :
      (x : R) →
      x ≠ zeroR →
      multiply x (reciprocal x) ≡ oneR

    order-reflexive :
      (x : R) → lessOrEqual x x
    order-transitive :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual y z →
      lessOrEqual x z
    order-antisymmetric :
      (x y : R) →
      lessOrEqual x y →
      lessOrEqual y x →
      x ≡ y
    order-total :
      (x y : R) → lessOrEqual x y ∨ lessOrEqual y x
    add-order :
      (x y z : R) →
      lessOrEqual x y →
      lessOrEqual (add z x) (add z y)
    multiply-nonnegative :
      (x y : R) →
      lessOrEqual zeroR x →
      lessOrEqual zeroR y →
      lessOrEqual zeroR (multiply x y)
    zero-less-than-one :
      lessOrEqual zeroR oneR ∧ zeroR ≠ oneR

    fromNat-zero :
      fromNat zero ≡ zeroR
    fromNat-successor :
      (n : Nat) → fromNat (suc n) ≡ add (fromNat n) oneR
    fromNat-addition :
      (m n : Nat) → fromNat (m + n) ≡ add (fromNat m) (fromNat n)
    fromNat-multiplication :
      (m n : Nat) →
      fromNat (m * n) ≡ multiply (fromNat m) (fromNat n)
    fromNat-injective :
      (m n : Nat) → fromNat m ≡ fromNat n → m ≡ n

    archimedean :
      (x : R) →
      Exists Nat (λ n → lessOrEqual x (fromNat n))
    least-upper-bound :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqual x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            P x →
            lessOrEqual x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              P x →
              lessOrEqual x upper) →
            lessOrEqual supremum upper))

open StandardReal

StrictLess :
  {R : Set} →
  StandardReal R →
  R →
  R →
  Set
StrictLess reals x y =
  lessOrEqual reals x y ∧ x ≠ y

intToReal :
  {R : Set} →
  StandardReal R →
  Int →
  R
intToReal reals (pos n) =
  fromNat reals n
intToReal reals (negsuc n) =
  negate reals (fromNat reals (suc n))

divide :
  {R : Set} →
  StandardReal R →
  R →
  R →
  R
divide reals x y =
  multiply reals x (reciprocal reals y)

record RealMaximum {R : Set} (reals : StandardReal R) : Set₁ where
  field
    maximum : R → R → R
    maximum-left :
      (x y : R) →
      lessOrEqual reals x (maximum x y)
    maximum-right :
      (x y : R) →
      lessOrEqual reals y (maximum x y)
    maximum-least :
      (x y upper : R) →
      lessOrEqual reals x upper →
      lessOrEqual reals y upper →
      lessOrEqual reals (maximum x y) upper

open RealMaximum

record RealCeiling {R : Set} (reals : StandardReal R) : Set₁ where
  field
    ceiling : R → Int
    ceiling-lower :
      (x : R) →
      StrictLess
        reals
        (intToReal reals (subtractInt (ceiling x) oneZ))
        x
    ceiling-upper :
      (x : R) →
      lessOrEqual reals x (intToReal reals (ceiling x))

open RealCeiling

module Statement
  {R : Set}
  (reals : StandardReal R)
  (maxima : RealMaximum reals)
  (ceilings : RealCeiling reals)
  where

  step : Int → R → R
  step n eps0 =
    multiply reals (intToReal reals n) eps0

  doubledStep : Int → R → R
  doubledStep n eps0 =
    multiply reals (fromNat reals twoN) (step n eps0)

  square : R → R
  square x =
    multiply reals x x

  shiftedSquare : R → R → R
  shiftedSquare x offset =
    square (add reals x offset)

  fact3Condition : R → R → Int → Bool → Set
  fact3Condition r eps0 n o1 =
    Conditional
      (StrictLess reals r (step n eps0))
      (Conditional
        (StrictLess reals (oneR reals) (step n eps0))
        (o1 ≡ true)
        (o1 ≡ false))
      (o1 ≡ false)

  doublingConclusion : R → R → Int → Bool → Set
  doublingConclusion r eps0 n o1 =
    Not (o1 ≡ true) →
    let
      o2 = multiplyInt twoZ n
      quotient =
        divide
          reals
          (maximum maxima r (oneR reals))
          eps0
      rounded = ceiling ceilings quotient
    in
    ((zeroZ ≤Z subtractInt rounded n)
      ∧
      (subtractInt rounded o2 <Z subtractInt rounded n))
    ∧
    lessOrEqual reals (zeroR reals) r
    ∧
    (StrictLess reals (zeroR reals) eps0 ∧ oneZ ≤Z o2)
    ∧
    (doubledStep n eps0
      ≡
      multiply reals (intToReal reals o2) eps0)

  resultAntecedent : R → R → Int → Bool → R → Set
  resultAntecedent r eps0 n o1 result =
    IfSet
      o1
      (result ≡ zeroR reals)
      (let
        o2 = doubledStep n eps0
       in
       Exists R
         (λ r′ →
           ((lessOrEqual reals (square r′) r
             ∧
             StrictLess reals r (shiftedSquare r′ o2))
           ∧
           Conditional
             (lessOrEqual
               reals
               (shiftedSquare r′ (step n eps0))
               r)
             (result ≡ add reals r′ (step n eps0))
             (result ≡ r′))))

  resultConclusion : R → R → Int → R → Set
  resultConclusion r eps0 n result =
    lessOrEqual reals (square result) r
    ∧
    StrictLess
      reals
      r
      (shiftedSquare result (step n eps0))

  proposition : Set
  proposition =
    (r eps0 : R) →
    (n : Int) →
    (o1 : Bool) →
    lessOrEqual reals (zeroR reals) r →
    StrictLess reals (zeroR reals) eps0 →
    oneZ ≤Z n →
    fact3Condition r eps0 n o1 →
    doublingConclusion r eps0 n o1
    ∧
    ((result : R) →
      resultAntecedent r eps0 n o1 result →
      resultConclusion r eps0 n result)

binary-sqrt-BinarySqrt-sqrt'vc : Set₁
binary-sqrt-BinarySqrt-sqrt'vc =
  (R : Set) →
  (reals : StandardReal R) →
  (maxima : RealMaximum reals) →
  (ceilings : RealCeiling reals) →
  Statement.proposition reals maxima ceilings
