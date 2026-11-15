-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/ropes_Rope_getqtvc: the rope character-access verification condition,
-- establishing valid recursive indexing and agreement with the flattened
-- string model. This file contains no proof.

{-# OPTIONS --safe #-}

module ropes_Rope_getqtvc where

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

branchObligation :
  (S : StringTheory) →
  Rope S →
  Int →
  Set
branchObligation S Emp i = ⊥
branchObligation S (Str s ofs len) i =
  let o1 = addInt ofs i
  in zeroZ ≤Z o1 ∧ o1 <Z stringLength S s
branchObligation S whole@(App left right len) i =
  let n = ropeLength left
  in IfSet
    (intLess i n)
    (containsChild whole left ∧
     ropeInvariant left ∧
     zeroZ ≤Z i ∧
     i <Z ropeLength left)
    (let o1 = subtractInt i n
     in containsChild whole right ∧
        ropeInvariant right ∧
        zeroZ ≤Z o1 ∧
        o1 <Z ropeLength right)

resultPremise :
  (S : StringTheory) →
  Rope S →
  Int →
  Char S →
  Set
resultPremise S Emp i result = ⊥
resultPremise S (Str s ofs len) i result =
  result ≡ stringIndex S s (addInt ofs i)
resultPremise S (App left right len) i result =
  let n = ropeLength left
  in IfSet
    (intLess i n)
    (result ≡ stringIndex S (ropeString left) i)
    (result ≡
     stringIndex S (ropeString right) (subtractInt i n))

resultObligation :
  (S : StringTheory) →
  Rope S →
  Int →
  Set
resultObligation S r i =
  (result : Char S) →
  resultPremise S r i result →
  result ≡ stringIndex S (ropeString r) i

GetVC :
  (S : StringTheory) →
  Rope S →
  Int →
  Set
GetVC S r i =
  ropeInvariant r →
  zeroZ ≤Z i →
  i <Z ropeLength r →
  branchObligation S r i ∧
  resultObligation S r i

ropes-Rope-getqtvc : Set₁
ropes-Rope-getqtvc =
  (S : StringTheory) →
  (r : Rope S) →
  (i : Int) →
  GetVC S r i
