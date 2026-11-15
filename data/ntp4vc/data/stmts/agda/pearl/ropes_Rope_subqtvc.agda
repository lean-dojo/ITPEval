-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/ropes_Rope_subqtvc: the rope substring verification condition,
-- preserving recursive-call validity and the invariant and flattened-string
-- specification of the resulting sub-rope. This file contains no proof.

{-# OPTIONS --safe #-}

module ropes_Rope_subqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_
infixr 2 _∨_

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

record _∧_ (A B : Set) : Set where
  constructor both
  field
    first  : A
    second : B

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

record Exists (A : Set) (P : A → Set) : Set where
  constructor witness
  field
    value    : A
    property : P value

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

IfSet : Bool → Set → Set → Set
IfSet true when-true when-false = when-true
IfSet false when-true when-false = when-false

zeroZ : Int
zeroZ = pos zero

record StringTheory : Set₁ where
  field
    Char       : Set
    CharString : Set

    dummyChar    : Char
    stringLength : CharString → Int
    stringIndex  : CharString → Int → Char
    emptyString  : CharString
    stringApp    : CharString → CharString → CharString
    stringSub    : CharString → Int → Int → CharString

    lengthNonnegative :
      (s : CharString) →
      zeroZ ≤Z stringLength s

    emptyLength :
      stringLength emptyString ≡ zeroZ

    stringExtensionality :
      (s1 s2 : CharString) →
      ((stringLength s1 ≡ stringLength s2) ∧
       ((i : Int) →
        (zeroZ ≤Z i ∧ i <Z stringLength s1) →
        stringIndex s1 i ≡ stringIndex s2 i)) →
      s1 ≡ s2

    appLength :
      (s1 s2 : CharString) →
      stringLength (stringApp s1 s2) ≡
      addInt (stringLength s1) (stringLength s2)

    appLeft :
      (s1 s2 : CharString) →
      (i : Int) →
      zeroZ ≤Z i →
      i <Z stringLength s1 →
      stringIndex (stringApp s1 s2) i ≡ stringIndex s1 i

    appRight :
      (s1 s2 : CharString) →
      (i : Int) →
      stringLength s1 ≤Z i →
      i <Z addInt (stringLength s1) (stringLength s2) →
      stringIndex (stringApp s1 s2) i ≡
      stringIndex s2 (subtractInt i (stringLength s1))

    subLength :
      (s : CharString) →
      (ofs len : Int) →
      zeroZ ≤Z len →
      zeroZ ≤Z ofs →
      ofs ≤Z stringLength s →
      addInt ofs len ≤Z stringLength s →
      stringLength (stringSub s ofs len) ≡ len

    subIndex :
      (s : CharString) →
      (ofs len i : Int) →
      zeroZ ≤Z len →
      zeroZ ≤Z ofs →
      ofs ≤Z stringLength s →
      addInt ofs len ≤Z stringLength s →
      zeroZ ≤Z i →
      i <Z len →
      stringIndex (stringSub s ofs len) i ≡
      stringIndex s (addInt ofs i)

open StringTheory

StringEqual :
  (S : StringTheory) →
  CharString S →
  CharString S →
  Set
StringEqual S s1 s2 =
  (stringLength S s1 ≡ stringLength S s2) ∧
  ((i : Int) →
   (zeroZ ≤Z i ∧ i <Z stringLength S s1) →
   stringIndex S s1 i ≡ stringIndex S s2 i)

data Rope (S : StringTheory) : Set where
  Emp : Rope S
  Str : CharString S → Int → Int → Rope S
  App : Rope S → Rope S → Int → Rope S

ropeLength : {S : StringTheory} → Rope S → Int
ropeLength Emp = zeroZ
ropeLength (Str _ _ len) = len
ropeLength (App _ _ len) = len

ropeInvariant : {S : StringTheory} → Rope S → Set
ropeInvariant {S} Emp = ⊤
ropeInvariant {S} (Str s ofs len) =
  zeroZ <Z len ∧
  (zeroZ ≤Z ofs ∧ ofs <Z stringLength S s) ∧
  addInt ofs len ≤Z stringLength S s
ropeInvariant {S} (App left right len) =
  zeroZ <Z ropeLength left ∧
  ropeInvariant left ∧
  zeroZ <Z ropeLength right ∧
  ropeInvariant right ∧
  len ≡ addInt (ropeLength left) (ropeLength right)

ropeString :
  {S : StringTheory} →
  Rope S →
  CharString S
ropeString {S} Emp = emptyString S
ropeString {S} (Str s ofs len) = stringSub S s ofs len
ropeString {S} (App left right _) =
  stringApp S (ropeString left) (ropeString right)

containsChild :
  {S : StringTheory} →
  Rope S →
  Rope S →
  Set
containsChild Emp child = ⊥
containsChild (Str _ _ _) child = ⊥
containsChild (App left right _) child =
  left ≡ child ∨ right ≡ child

SubCallPrecondition :
  (S : StringTheory) →
  Rope S →
  Rope S →
  Int →
  Int →
  Set
SubCallPrecondition S parent child ofs len =
  containsChild parent child ∧
  ropeInvariant child ∧
  zeroZ ≤Z len ∧
  (zeroZ ≤Z ofs ∧ ofs ≤Z ropeLength child) ∧
  addInt ofs len ≤Z ropeLength child

SubResult :
  (S : StringTheory) →
  Rope S →
  Int →
  Int →
  Rope S →
  Set
SubResult S source ofs len result =
  ropeInvariant result ∧
  StringEqual S
    (ropeString result)
    (stringSub S (ropeString source) ofs len)

branchObligation :
  (S : StringTheory) →
  Rope S →
  Int →
  Int →
  Set
branchObligation S Emp len ofs = ⊤
branchObligation S (Str s storedOfs storedLen) len ofs = ⊤
branchObligation S whole@(App left right storedLen) len ofs =
  let
    leftCount = subtractInt (ropeLength left) ofs
    rightCount = subtractInt len leftCount
  in
  IfSet
    (intLessOrEqual rightCount zeroZ)
    (SubCallPrecondition S whole left ofs len)
    (IfSet
      (intLessOrEqual leftCount zeroZ)
      (SubCallPrecondition
        S whole right (negateInt leftCount) len)
      (SubCallPrecondition S whole right zeroZ rightCount ∧
       ((rightResult : Rope S) →
        SubResult S right zeroZ rightCount rightResult →
        SubCallPrecondition S whole left ofs leftCount ∧
        ((leftResult : Rope S) →
         SubResult S left ofs leftCount leftResult →
         ropeInvariant leftResult ∧
         ropeInvariant rightResult))))

executionPremise :
  (S : StringTheory) →
  Rope S →
  Int →
  Int →
  Rope S →
  Set
executionPremise S Emp len ofs result =
  result ≡ Emp
executionPremise S (Str s storedOfs storedLen) len ofs result =
  IfSet
    (intEqual len zeroZ)
    (result ≡ Emp)
    (result ≡ Str s (addInt storedOfs ofs) len)
executionPremise S (App left right storedLen) len ofs result =
  let
    leftCount = subtractInt (ropeLength left) ofs
    rightCount = subtractInt len leftCount
  in
  IfSet
    (intLessOrEqual rightCount zeroZ)
    (SubResult S left ofs len result)
    (IfSet
      (intLessOrEqual leftCount zeroZ)
      (SubResult S right (negateInt leftCount) len result)
      (Exists
        (Rope S)
        (λ rightResult →
          SubResult S right zeroZ rightCount rightResult ∧
          Exists
            (Rope S)
            (λ leftResult →
              SubResult S left ofs leftCount leftResult ∧
              ropeInvariant result ∧
              StringEqual S
                (ropeString result)
                (stringApp S
                  (ropeString leftResult)
                  (ropeString rightResult))))))

resultObligation :
  (S : StringTheory) →
  Rope S →
  Int →
  Int →
  Set
resultObligation S source len ofs =
  (result : Rope S) →
  executionPremise S source len ofs result →
  SubResult S source ofs len result

SubVC :
  (S : StringTheory) →
  Rope S →
  Int →
  Int →
  Set
SubVC S r len ofs =
  ropeInvariant r →
  zeroZ ≤Z len →
  zeroZ ≤Z ofs →
  ofs ≤Z ropeLength r →
  addInt ofs len ≤Z ropeLength r →
  branchObligation S r len ofs ∧
  resultObligation S r len ofs

ropes-Rope-subqtvc : Set₁
ropes-Rope-subqtvc =
  (S : StringTheory) →
  (r : Rope S) →
  (len ofs : Int) →
  SubVC S r len ofs
