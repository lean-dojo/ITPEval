-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_push_Why3_ide_VClist_push_does_not_contain_item_post_Separation_part1_goal54:
-- the final list-push pointer-memory updates keep the updated array entry at
-- the designated index separated from the full array allocation, under the
-- stated linked-list, integer-bound, memory-validity, separation, framing,
-- unchanged-region, and pointer-distinctness assumptions, with pointer-array
-- indices scaled by eight bytes and raw shifts retained for fields and
-- imported predicates. This file contains no proof.

{-# OPTIONS --safe #-}

module list_push_Why3_ide_VClist_push_does_not_contain_item_post_Separation_part1_goal54 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

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

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

record Iff (A B : Set) : Set where
  constructor equivalence
  field
    forward  : A → B
    backward : B → A

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

notBool : Bool → Bool
notBool true = false
notBool false = true

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

ifBool : {A : Set} → Bool → A → A → A
ifBool true yes _ = yes
ifBool false _ no = no

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

zeroZ oneZ twoZ threeZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
twoZ = pos (suc (suc zero))
threeZ = pos (suc (suc (suc zero)))
fourZ = pos (suc (suc (suc (suc zero))))

maximumArrayIndex maximumArrayIndexMinusOne signed32Lower signed32Upper : Int
maximumArrayIndex = pos 2147483646
maximumArrayIndexMinusOne = pos 2147483645
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record CompleteOrderedField (R : Set) : Set₁ where
  field
    zeroR oneR : R
    addR multiplyR : R → R → R
    negateR reciprocalR : R → R
    lessOrEqualR : R → R → Set
    fromNatR : Nat → R

    one-not-zeroR :
      oneR ≠ zeroR

    add-commutativeR :
      (x y : R) → addR x y ≡ addR y x
    add-associativeR :
      (x y z : R) →
      addR (addR x y) z ≡ addR x (addR y z)
    add-zeroR :
      (x : R) → addR x zeroR ≡ x
    add-inverseR :
      (x : R) → addR x (negateR x) ≡ zeroR

    multiply-commutativeR :
      (x y : R) → multiplyR x y ≡ multiplyR y x
    multiply-associativeR :
      (x y z : R) →
      multiplyR (multiplyR x y) z ≡
      multiplyR x (multiplyR y z)
    multiply-oneR :
      (x : R) → multiplyR x oneR ≡ x
    multiply-zeroR :
      (x : R) → multiplyR x zeroR ≡ zeroR
    distributeR :
      (x y z : R) →
      multiplyR x (addR y z) ≡
      addR (multiplyR x y) (multiplyR x z)
    reciprocal-zeroR :
      reciprocalR zeroR ≡ zeroR
    multiply-reciprocalR :
      (x : R) →
      x ≠ zeroR →
      multiplyR x (reciprocalR x) ≡ oneR

    order-reflexiveR :
      (x : R) → lessOrEqualR x x
    order-transitiveR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR y z →
      lessOrEqualR x z
    order-antisymmetricR :
      (x y : R) →
      lessOrEqualR x y →
      lessOrEqualR y x →
      x ≡ y
    order-totalR :
      (x y : R) →
      Either (lessOrEqualR x y) (lessOrEqualR y x)
    add-orderR :
      (x y z : R) →
      lessOrEqualR x y →
      lessOrEqualR (addR z x) (addR z y)
    multiply-nonnegativeR :
      (x y : R) →
      lessOrEqualR zeroR x →
      lessOrEqualR zeroR y →
      lessOrEqualR zeroR (multiplyR x y)
    zero-less-than-oneR :
      (lessOrEqualR zeroR oneR) ∧ (zeroR ≠ oneR)

    fromNat-zeroR :
      fromNatR zero ≡ zeroR
    fromNat-successorR :
      (n : Nat) →
      fromNatR (suc n) ≡ addR (fromNatR n) oneR
    fromNat-additionR :
      (m n : Nat) →
      fromNatR (m + n) ≡ addR (fromNatR m) (fromNatR n)
    fromNat-multiplicationR :
      (m n : Nat) →
      fromNatR (m * n) ≡ multiplyR (fromNatR m) (fromNatR n)
    fromNat-injectiveR :
      (m n : Nat) →
      fromNatR m ≡ fromNatR n →
      m ≡ n

    archimedeanR :
      (x : R) →
      Exists Nat (λ n → lessOrEqualR x (fromNatR n))
    least-upper-boundR :
      (P : R → Set) →
      Exists R P →
      Exists R
        (λ upper →
          (x : R) →
          P x →
          lessOrEqualR x upper) →
      Exists R
        (λ supremum →
          ((x : R) →
            P x →
            lessOrEqualR x supremum)
          ∧
          ((upper : R) →
            ((x : R) →
              P x →
              lessOrEqualR x upper) →
            lessOrEqualR supremum upper))

open CompleteOrderedField

record CompleteOrderedFieldEquivalence
  {R S : Set}
  (source : CompleteOrderedField R)
  (target : CompleteOrderedField S) : Set₁ where
  field
    forwardR : R → S
    backwardR : S → R
    forward-after-backwardR :
      (y : S) → forwardR (backwardR y) ≡ y
    backward-after-forwardR :
      (x : R) → backwardR (forwardR x) ≡ x
    forward-zeroR :
      forwardR (zeroR source) ≡ zeroR target
    forward-oneR :
      forwardR (oneR source) ≡ oneR target
    forward-addR :
      (x y : R) →
      forwardR (addR source x y) ≡
      addR target (forwardR x) (forwardR y)
    forward-multiplyR :
      (x y : R) →
      forwardR (multiplyR source x y) ≡
      multiplyR target (forwardR x) (forwardR y)
    forward-negateR :
      (x : R) →
      forwardR (negateR source x) ≡ negateR target (forwardR x)
    forward-reciprocalR :
      (x : R) →
      forwardR (reciprocalR source x) ≡
      reciprocalR target (forwardR x)
    forward-fromNatR :
      (n : Nat) →
      forwardR (fromNatR source n) ≡ fromNatR target n
    forward-orderR :
      (x y : R) →
      Iff
        (lessOrEqualR source x y)
        (lessOrEqualR target (forwardR x) (forwardR y))

record RealNumberPresentation
  {R : Set}
  (reals : CompleteOrderedField R) : Set₂ where
  field
    equivalent-complete-ordered-field :
      (S : Set) →
      (other : CompleteOrderedField S) →
      CompleteOrderedFieldEquivalence reals other

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

timesEight : Int → Int
timesEight k =
  let
    twice = addInt k k
    four-times = addInt twice twice
  in
  addInt four-times four-times

shiftPtr : Addr → Int → Addr
shiftPtr p k = shift p k

addrEqual : Addr → Addr → Bool
addrEqual p q =
  andBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

separatedBool : Addr → Int → Addr → Int → Bool
separatedBool p a q b =
  orBool (intLessOrEqual a zeroZ)
    (orBool (intLessOrEqual b zeroZ)
      (orBool (notBool (intEqual (base p) (base q)))
        (orBool
          (intLessOrEqual (addInt (offset q) b) (offset p))
          (intLessOrEqual (addInt (offset p) a) (offset q)))))

Separated : Addr → Int → Addr → Int → Set
Separated p a q b = separatedBool p a q b ≡ true

havoc :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Addr →
  Addr
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

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record S1List (R : Set) : Set where
  constructor s1list
  field
    next : Addr
    x-coordinate : R
    y-coordinate : R
    z-coordinate : R

open S1List

loadS1List :
  {R : Set} →
  Addr →
  (Addr → R) →
  (Addr → Addr) →
  S1List R
loadS1List p float-memory pointer-memory =
  s1list
    (pointer-memory (shift p zeroZ))
    (float-memory (shift p oneZ))
    (float-memory (shift p twoZ))
    (float-memory (shift p threeZ))

EqS1List : {R : Set} → S1List R → S1List R → Set
EqS1List first-list second-list =
  (next second-list ≡ next first-list) ∧
  (x-coordinate second-list ≡ x-coordinate first-list) ∧
  (y-coordinate second-list ≡ y-coordinate first-list) ∧
  (z-coordinate second-list ≡ z-coordinate first-list)

record IndexOfTheory : Set where
  field
    lIndexOf :
      (Addr → Addr) →
      Addr →
      Addr →
      Int →
      Int →
      Int

    no-more-elements :
      (up down : Int) →
      (pointer-memory : Addr → Addr) →
      (item array : Addr) →
      up ≤Z down →
      zeroZ ≤Z up →
      lIndexOf pointer-memory item array down up ≡ up

    found-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shift array down) ≡ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf pointer-memory item array down up ≡ down

    not-the-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shift array down) ≠ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf
        pointer-memory item array (addInt oneZ down) up ≡
      lIndexOf pointer-memory item array down up

data PLinkedN :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Addr →
  Int →
  Int →
  Addr →
  Set where

  linked-bound :
    (index : Int) →
    (allocation : Int → Int) →
    (pointer-memory : Addr → Addr) →
    (bound array : Addr) →
    zeroZ ≤Z index →
    index ≤Z maximumArrayIndex →
    PLinkedN
      allocation pointer-memory bound array index zeroZ bound

  linked-cons :
    (index n : Int) →
    (pointer-memory : Addr → Addr) →
    (array root : Addr) →
    (allocation : Int → Int) →
    (bound : Addr) →
    pointer-memory (shift array index) ≡ root →
    zeroZ <Z n →
    zeroZ ≤Z index →
    zeroZ ≤Z addInt index n →
    addInt index n ≤Z maximumArrayIndex →
    ValidRW allocation root fourZ →
    PLinkedN
      allocation
      pointer-memory
      (pointer-memory (shift root zeroZ))
      array
      (addInt oneZ index)
      (subtractInt n oneZ)
      bound →
    PLinkedN
      allocation pointer-memory root array index n bound

PUnchanged :
  {R : Set} →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → R) →
  (Int → Int) →
  (Addr → Addr) →
  (Addr → R) →
  Addr →
  Int →
  Int →
  Set
PUnchanged
  allocation0 pointer-memory0 float-memory0
  allocation1 pointer-memory1 float-memory1
  array down up =
  (index : Int) →
  let
    location = shift array index
    pointer0 = pointer-memory0 location
    pointer1 = pointer-memory1 location
  in
  down ≤Z index →
  index <Z up →
  (pointer0 ≡ pointer1) ∧
  EqS1List
    (loadS1List pointer1 float-memory1 pointer-memory1)
    (loadS1List pointer0 float-memory0 pointer-memory0) ∧
  (ValidRW allocation1 pointer1 fourZ →
   ValidRW allocation0 pointer0 fourZ)

PArraySwipeRight :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
PArraySwipeRight pointer-memory0 pointer-memory1 array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  pointer-memory1
    (shift array (subtractInt index oneZ)) ≡
  pointer-memory0 (shift array index)

module VC54
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal54 : Set
  goal54 =
    (i i1 : Int) →
    (t3 : Addr → Addr) →
    (a3 a4 a2 : Addr) →
    (t2 : Addr → Addr) →
    (a a1 : Addr) →
    (t4 : Addr → Addr) →
    (i2 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      x = subtractInt i oneZ
      x1 = subtractInt (addInt i i1) oneZ
      x2 = lIndexOf t3 a3 a4 x x1
      x3 = addInt oneZ x2
      x4 = addInt i i1
      a5 = shiftPtr a4 zeroZ
      a6 = t3 a2
      a7 = shiftPtr a4 x
      a8 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift
              (t3 (shiftPtr a4 (subtractInt x2 oneZ)))
              zeroZ)
            a1)
          (shiftPtr a4 x2)
          (subtractInt x1 x2)
      a9 = a8 a2
      a13 =
        havoc
          t4
          a8
          a7
          (addInt oneZ i1)
      a10 =
        update
          (update a13 (shift a3 zeroZ) a9)
          a7
          a3
      a11 = update a10 a2 a3
    in
    addr zeroZ zeroZ ≠ a3 →
    x3 ≡ x4 →
    zeroZ <Z i →
    zeroZ ≤Z i1 →
    i2 <Z x4 →
    region (Addr.base a2) ≤Z zeroZ →
    region (Addr.base a3) ≤Z zeroZ →
    region (Addr.base a4) ≤Z zeroZ →
    x2 <Z x4 →
    i1 ≤Z maximumArrayIndexMinusOne →
    x4 ≤Z maximumArrayIndex →
    i ≤Z addInt oneZ i2 →
    i ≤Z x3 →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation a2 oneZ →
    ValidRW allocation a3 fourZ →
    Separated a2 oneZ a3 fourZ →
    IsSint32 x →
    ValidRW allocation a5 maximumArrayIndex →
    Separated a2 oneZ a5 maximumArrayIndex →
    Separated a3 fourZ a5 maximumArrayIndex →
    Separated a6 fourZ a5 maximumArrayIndex →
    ValidRW allocation a7 i1 →
    PLinkedN
      allocation t3 a6 a4 x i1
      (addr zeroZ zeroZ) →
    IsSint32 x2 →
    Separated a9 fourZ a5 maximumArrayIndex →
    EqS1List
      (loadS1List a3 float-memory a8)
      (loadS1List a3 float-memory t3) →
    PLinkedN
      allocation a8 a9 a4 x i1
      (addr zeroZ zeroZ) →
    PUnchanged
      allocation a8 float-memory
      allocation t3 float-memory
      a4 x x1 →
    PUnchanged
      allocation a11 float-memory
      allocation a10 float-memory
      a4 x x4 →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      t3 (shiftPtr a4 index) ≠ a3) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      IsSint32 index →
      t3 (shiftPtr a4 index) ≠ a3) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        a2 oneZ
        (t3 (shiftPtr a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        (t3 (shiftPtr a4 index)) fourZ
        a5 maximumArrayIndex) →
    ((index : Int) →
      let node = t3 (shiftPtr a4 index)
      in
      node ≠ a3 →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated a3 fourZ node fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      t3 (shiftPtr a4 left-index) ≠
      t3 (shiftPtr a4 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      Separated
        (t3 (shiftPtr a4 left-index)) fourZ
        (t3 (shiftPtr a4 right-index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      a8 (shiftPtr a4 index) ≠ a3) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        a2 oneZ
        (a8 (shiftPtr a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        a3 fourZ
        (a8 (shiftPtr a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        (a8 (shiftPtr a4 index)) fourZ
        a5 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      a8 (shiftPtr a4 left-index) ≠
      a8 (shiftPtr a4 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      Separated
        (a8 (shiftPtr a4 left-index)) fourZ
        (a8 (shiftPtr a4 right-index)) fourZ) →
    a13 a2 ≡ a9 →
    Separated
      (a13 a2) fourZ
      a5 maximumArrayIndex →
    ((index : Int) →
      i ≤Z index →
      index <Z x4 →
      Separated
        a2 oneZ
        (a13 (shiftPtr a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z index →
      index <Z x4 →
      Separated
        (a13 (shiftPtr a4 index)) fourZ
        a5 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z right-index →
      i ≤Z left-index →
      right-index <Z x4 →
      left-index <Z x4 →
      Separated
        (a13 (shiftPtr a4 left-index)) fourZ
        (a13 (shiftPtr a4 right-index)) fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      x ≤Z right-index →
      x ≤Z left-index →
      right-index <Z x4 →
      left-index <Z x4 →
      a13 (shiftPtr a4 left-index) ≠
      a13 (shiftPtr a4 right-index)) →
    PArraySwipeRight a13 a8 a4 i x4 →
    PLinkedN
      allocation a13 a9 a4 i i1
      (addr zeroZ zeroZ) →
    Separated
      (a11 (shiftPtr a4 i2)) fourZ
      a5 maximumArrayIndex

list-push-does-not-contain-item-post-separation-part1-goal54 : Set₂
list-push-does-not-contain-item-post-separation-part1-goal54 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC54.goal54 {R} region linked index-of-theory
