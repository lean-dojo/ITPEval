-- Statement-only formalization of the NTP4VC corpus artifact
-- pearl/ropes_Balance_insert_leavesqtvc: the rope leaf-insertion verification
-- condition preserving queue rope invariants and appending the inserted
-- rope's modeled string. This file contains no proof.

{-# OPTIONS --safe #-}

module ropes_Balance_insert_leavesqtvc where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.List using (List; []; _∷_)
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
  or-left  : A → A ∨ B
  or-right : B → A ∨ B

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

module InsertLeavesStatement
  (S : StringTheory)
  (B : BalanceTheory S)
  where

  stringOfQueue :
    List (Rope S) →
    CharString S
  stringOfQueue q =
    stringOfArray B q twoZ (natToInt (length q))

  AllInvariant :
    List (Rope S) →
    Set
  AllInvariant q =
    (j : Int) →
    (twoZ ≤Z j ∧ j ≤Z maximum B) →
    ropeInvariant (nthDefault Emp (intToNat j) q)

  PrefixUnchanged :
    List (Rope S) →
    List (Rope S) →
    Set
  PrefixUnchanged q1 q =
    (j : Int) →
    (twoZ ≤Z j ∧ j <Z twoZ) →
    nthDefault Emp (intToNat j) q1 ≡
    nthDefault Emp (intToNat j) q

  IsChild :
    Rope S →
    Rope S →
    Set
  IsChild Emp child = ⊥
  IsChild (Str _ _ _) child = ⊥
  IsChild (App first second _) child =
    first ≡ child ∨ second ≡ child

  EmptyBranch :
    List (Rope S) →
    Rope S →
    Set
  EmptyBranch q source =
    AllInvariant q ∧
    StringEqual S
      (stringOfQueue q)
      (stringApp S
        (stringOfQueue q)
        (ropeString source))

  InsertPostcondition :
    List (Rope S) →
    Rope S →
    Set
  InsertPostcondition q source =
    (q1 : List (Rope S)) →
    length q1 ≡ length q →
    (AllInvariant q1 ∧
     PrefixUnchanged q1 q ∧
     StringEqual S
       (stringOfArray B
         q1
         twoZ
         (addInt (maximum B) oneZ))
       (stringApp S
         (stringOfArray B
           q
           twoZ
           (addInt (maximum B) oneZ))
         (ropeString source))) →
    AllInvariant q1 ∧
    StringEqual S
      (stringOfQueue q1)
      (stringApp S
        (stringOfQueue q)
        (ropeString source))

  StringBranch :
    List (Rope S) →
    Rope S →
    Set
  StringBranch q source =
    (((twoZ ≤Z twoZ ∧
       twoZ <Z natToInt (length q) ∧
       natToInt (length q) ≡
         addInt (maximum B) oneZ) ∧
      ropeInvariant source ∧
      AllInvariant q ∧
      addInt
        (stringLength S
          (stringOfArray B
            q
            twoZ
            (addInt (maximum B) oneZ)))
        (ropeLength source)
        <Z fib B (addInt (maximum B) oneZ)) ∧
     InsertPostcondition q source)

  RecursiveCallPrecondition :
    Rope S →
    List (Rope S) →
    Rope S →
    Set
  RecursiveCallPrecondition parent q child =
    IsChild parent child ∧
    (twoZ <Z natToInt (length q) ∧
     natToInt (length q) ≡
       addInt (maximum B) oneZ) ∧
    ropeInvariant child ∧
    AllInvariant q ∧
    addInt
      (stringLength S (stringOfQueue q))
      (ropeLength child)
      <Z fib B (addInt (maximum B) oneZ)

  RightCallContinuation :
    Rope S →
    List (Rope S) →
    List (Rope S) →
    Rope S →
    Set
  RightCallContinuation parent original q1 rightChild =
    (q2 : List (Rope S)) →
    length q2 ≡ length q1 →
    (AllInvariant q2 ∧
     StringEqual S
       (stringOfQueue q2)
       (stringApp S
         (stringOfQueue q1)
         (ropeString rightChild))) →
    AllInvariant q2 ∧
    StringEqual S
      (stringOfQueue q2)
      (stringApp S
        (stringOfQueue original)
        (ropeString parent))

  LeftCallContinuation :
    Rope S →
    List (Rope S) →
    Rope S →
    Rope S →
    Set
  LeftCallContinuation parent original leftChild rightChild =
    (q1 : List (Rope S)) →
    length q1 ≡ length original →
    (AllInvariant q1 ∧
     StringEqual S
       (stringOfQueue q1)
       (stringApp S
         (stringOfQueue original)
         (ropeString leftChild))) →
    RecursiveCallPrecondition parent q1 rightChild ∧
    RightCallContinuation parent original q1 rightChild

  AppBranch :
    List (Rope S) →
    Rope S →
    Rope S →
    Rope S →
    Set
  AppBranch q source leftChild rightChild =
    RecursiveCallPrecondition source q leftChild ∧
    LeftCallContinuation source q leftChild rightChild

  BranchConclusion :
    List (Rope S) →
    Rope S →
    Set
  BranchConclusion q source@Emp =
    EmptyBranch q source
  BranchConclusion q source@(Str _ _ _) =
    StringBranch q source
  BranchConclusion q source@(App leftChild rightChild _) =
    AppBranch q source leftChild rightChild

  InsertLeavesVC :
    List (Rope S) →
    Rope S →
    Set
  InsertLeavesVC q source =
    twoZ <Z natToInt (length q) →
    natToInt (length q) ≡ addInt (maximum B) oneZ →
    ropeInvariant source →
    AllInvariant q →
    addInt
      (stringLength S (stringOfQueue q))
      (ropeLength source)
      <Z fib B (addInt (maximum B) oneZ) →
    BranchConclusion q source

insert-leaves'vc : Set₁
insert-leaves'vc =
  (S : StringTheory) →
  (B : BalanceTheory S) →
  (q : List (Rope S)) →
  (source : Rope S) →
  InsertLeavesStatement.InsertLeavesVC S B q source
