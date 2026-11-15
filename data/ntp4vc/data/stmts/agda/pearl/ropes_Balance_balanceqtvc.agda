-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/ropes_Balance_balanceqtvc: the rope-balancing verification condition
-- for queue initialization, leaf insertion, and reconstruction of a valid
-- rope with the same modeled string. This file contains no proof.

{-# OPTIONS --safe #-}

module ropes_Balance_balanceqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

infix 4 _≤Z_ _<Z_
infixr 3 _∧_

data ⊤ : Set where
  tt : ⊤

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

intToNat : Int → Nat
intToNat (pos n) = n
intToNat (negsuc _) = zero

natToInt : Nat → Int
natToInt = pos

ifInt : Bool → Int → Int → Int
ifInt true when-true when-false = when-true
ifInt false when-true when-false = when-false

zeroZ oneZ twoZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))

length : {A : Set} → List A → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

nthDefault : {A : Set} → A → Nat → List A → A
nthDefault default zero [] = default
nthDefault default zero (x ∷ xs) = x
nthDefault default (suc n) [] = default
nthDefault default (suc n) (_ ∷ xs) = nthDefault default n xs

record StringTheory : Set₁ where
  field
    Char       : Set
    CharString : Set

    dummyChar   : Char
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

record BalanceTheory (S : StringTheory) : Set₁ where
  field
    fib : Int → Int

    fibDefinition :
      (n : Int) →
      zeroZ ≤Z n →
      fib n ≡
      ifInt
        (intEqual n zeroZ)
        zeroZ
        (ifInt
          (intEqual n oneZ)
          oneZ
          (addInt
            (fib (subtractInt n oneZ))
            (fib (subtractInt n twoZ))))

    maximum :
      Int

    maximumDefinition :
      twoZ ≤Z maximum

    stringOfArray :
      List (Rope S) →
      Int →
      Int →
      CharString S

    stringOfArrayEmpty :
      (l : Int) →
      (q : List (Rope S)) →
      zeroZ ≤Z l →
      l ≤Z natToInt (length q) →
      StringEqual S
        (stringOfArray q l l)
        (emptyString S)

    stringOfArrayConcatLeft :
      (l u : Int) →
      (q : List (Rope S)) →
      zeroZ ≤Z l →
      l <Z u →
      u ≤Z natToInt (length q) →
      StringEqual S
        (stringOfArray q l u)
        (stringApp S
          (stringOfArray q (addInt l oneZ) u)
          (ropeString
            (nthDefault Emp (intToNat l) q)))

open BalanceTheory

module BalanceStatement
  (S : StringTheory)
  (B : BalanceTheory S)
  where

  stringOfQueue :
    List (Rope S) →
    CharString S
  stringOfQueue q =
    stringOfArray B q twoZ (natToInt (length q))

  AllEmpty :
    List (Rope S) →
    Int →
    Set
  AllEmpty q upper =
    (i : Int) →
    (zeroZ ≤Z i ∧ i <Z upper) →
    nthDefault Emp (intToNat i) q ≡ Emp

  AllInvariant :
    List (Rope S) →
    Int →
    Int →
    Set
  AllInvariant q lower upper =
    (j : Int) →
    (lower ≤Z j ∧ j ≤Z upper) →
    ropeInvariant (nthDefault Emp (intToNat j) q)

  LoopIndexObligation :
    List (Rope S) →
    Int →
    Rope S →
    Set
  LoopIndexObligation q upper current =
    (i : Int) →
    ((twoZ ≤Z i ∧ i ≤Z upper) ∧
     ropeInvariant current ∧
     StringEqual S
       (ropeString current)
       (stringOfArray B q twoZ i)) →
    (zeroZ ≤Z i ∧ i <Z natToInt (length q)) ∧
    (let item = nthDefault Emp (intToNat i) q
     in
     (ropeInvariant item ∧ ropeInvariant current) ∧
     ((combined : Rope S) →
      (ropeInvariant combined ∧
       StringEqual S
         (ropeString combined)
         (stringApp S
           (ropeString item)
           (ropeString current))) →
      ropeInvariant combined ∧
      StringEqual S
        (ropeString combined)
        (stringOfArray B q twoZ (addInt i oneZ))))

  LoopResultObligations :
    List (Rope S) →
    Rope S →
    Int →
    Set
  LoopResultObligations q source upper =
    (current : Rope S) →
    LoopIndexObligation q upper current ∧
    ((ropeInvariant current ∧
      StringEqual S
        (ropeString current)
        (stringOfArray B q twoZ (addInt upper oneZ))) →
     ropeInvariant current ∧
     StringEqual S
       (ropeString current)
       (ropeString source))

  FoldObligations :
    List (Rope S) →
    Rope S →
    Set
  FoldObligations q source =
    (twoZ ≤Z addInt (maximum B) oneZ →
     (ropeInvariant (Emp {S = S}) ∧
      StringEqual S
        (ropeString (Emp {S = S}))
        (stringOfArray B q twoZ twoZ)) ∧
     LoopResultObligations q source (maximum B)) ∧
    (addInt (maximum B) oneZ <Z twoZ →
     ropeInvariant (Emp {S = S}) ∧
     StringEqual S
       (ropeString (Emp {S = S}))
       (ropeString source))

  InsertLeavesPostcondition :
    List (Rope S) →
    Rope S →
    Set
  InsertLeavesPostcondition q source =
    (q1 : List (Rope S)) →
    length q1 ≡ length q →
    (AllInvariant q1 twoZ (maximum B) ∧
     StringEqual S
       (stringOfQueue q1)
       (stringApp S
         (stringOfQueue q)
         (ropeString source))) →
    FoldObligations q1 source

  InitialQueueBody :
    List (Rope S) →
    Rope S →
    Set
  InitialQueueBody q source =
    ((twoZ <Z natToInt (length q) ∧
      natToInt (length q) ≡ addInt (maximum B) oneZ) ∧
     ropeInvariant source ∧
     AllInvariant q twoZ (maximum B) ∧
     addInt
       (stringLength S (stringOfQueue q))
       (ropeLength source)
       <Z fib B (addInt (maximum B) oneZ)) ∧
    InsertLeavesPostcondition q source

  InitialQueueObligations :
    Rope S →
    Int →
    Set
  InitialQueueObligations source upper =
    (q : List (Rope S)) →
    (AllEmpty q upper ∧
     natToInt (length q) ≡ upper) →
    InitialQueueBody q source

  BalanceVC :
    Rope S →
    Set
  BalanceVC source =
    ropeInvariant source →
    ropeLength source <Z fib B (addInt (maximum B) oneZ) →
    zeroZ ≤Z addInt (maximum B) oneZ ∧
    InitialQueueObligations
      source
      (addInt (maximum B) oneZ)

balance'vc : Set₁
balance'vc =
  (S : StringTheory) →
  (B : BalanceTheory S) →
  (source : Rope S) →
  BalanceStatement.BalanceVC S B source
