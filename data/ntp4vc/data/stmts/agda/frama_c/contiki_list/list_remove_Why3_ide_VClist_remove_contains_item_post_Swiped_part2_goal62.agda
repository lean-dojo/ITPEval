-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part2_goal62:
-- the list-removal verification condition states that updating the head
-- pointer to its successor makes the remaining array segment a left swipe
-- of the updated pointer memory, under the stated integer bounds, memory
-- validity, framing, linked-list, separation, index-of, and distinctness
-- assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part2_goal62 where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

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

andBool : Bool → Bool → Bool
andBool true b = b
andBool false _ = false

orBool : Bool → Bool → Bool
orBool true _ = true
orBool false b = b

notBool : Bool → Bool
notBool true = false
notBool false = true

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

zeroZ oneZ fourZ : Int
zeroZ = pos zero
oneZ = pos (suc zero)
fourZ = pos (suc (suc (suc (suc zero))))

maximumArrayIndex maximumArrayIndexMinusOne signed32Lower signed32Upper : Int
maximumArrayIndex = pos 2147483646
maximumArrayIndexMinusOne = pos 2147483645
signed32Lower = negsuc 2147483647
signed32Upper = pos 2147483648

record Addr : Set where
  constructor addr
  field
    base   : Int
    offset : Int

open Addr

shift : Addr → Int → Addr
shift p k = addr (base p) (addInt (offset p) k)

addrEqual : Addr → Addr → Bool
addrEqual p q =
  andBool
    (intEqual (base p) (base q))
    (intEqual (offset p) (offset q))

separatedBool : Addr → Int → Addr → Int → Bool
separatedBool p a q b =
  orBool
    (intLessOrEqual a zeroZ)
    (orBool
      (intLessOrEqual b zeroZ)
      (orBool
        (notBool (intEqual (base p) (base q)))
        (orBool
          (intLessOrEqual (addInt (offset q) b) (offset p))
          (intLessOrEqual (addInt (offset p) a) (offset q)))))

update : {A : Set} → (Addr → A) → Addr → A → Addr → A
update memory location value query =
  ifBool (addrEqual query location) value (memory query)

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

Separated : Addr → Int → Addr → Int → Set
Separated p a q b =
  Either
    (a ≤Z zeroZ)
    (Either
      (b ≤Z zeroZ)
      (Either
        (base p ≠ base q)
        (Either
          (addInt (offset q) b ≤Z offset p)
          (addInt (offset p) a ≤Z offset q))))

IsSint32 : Int → Set
IsSint32 x =
  (signed32Lower ≤Z x) ∧
  (x <Z signed32Upper)

record IndexOfTheory : Set where
  field
    lIndexOf :
      (Addr → Addr) → Addr → Addr → Int → Int → Int

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

PArraySwipeLeft :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
PArraySwipeLeft old-memory new-memory array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  new-memory (shift array (addInt oneZ index)) ≡
  old-memory (shift array index)

module VC62
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (base (pointer-memory p)) ≤Z zeroZ

  goal62 : Set
  goal62 =
    (pointer-memory : Addr → Addr) →
    (post-memory havoc-memory : Addr → Addr) →
    (head array : Addr) →
    (item-index length start-index : Int) →
    (allocation : Int → Int) →
    let
      root = pointer-memory head
      item = pointer-memory (shift array item-index)
      upper = addInt length start-index
      array-start = shift array zeroZ
      selected-index =
        lIndexOf pointer-memory item array start-index upper
      root-next = pointer-memory (shift root zeroZ)
    in
    root ≠ addr zeroZ zeroZ →
    item ≠ addr zeroZ zeroZ →
    item ≡ root →
    zeroZ ≤Z length →
    zeroZ ≤Z start-index →
    start-index ≤Z item-index →
    item-index <Z upper →
    region (base head) ≤Z zeroZ →
    region (base array) ≤Z zeroZ →
    region (base root) ≤Z zeroZ →
    length ≤Z maximumArrayIndexMinusOne →
    Framed pointer-memory →
    linked allocation →
    IsSint32 length →
    IsSint32 start-index →
    ValidRW allocation head oneZ →
    ValidRW allocation array-start maximumArrayIndex →
    Separated head oneZ array-start maximumArrayIndex →
    Separated root fourZ array-start maximumArrayIndex →
    PLinkedN
      allocation pointer-memory root array start-index length
      (addr zeroZ zeroZ) →
    IsSint32 selected-index →
    ((index : Int) →
      start-index ≤Z index →
      index <Z upper →
      Separated
        head oneZ
        (pointer-memory (shift array index)) fourZ) →
    ((index : Int) →
      start-index ≤Z index →
      index <Z upper →
      Separated
        (pointer-memory (shift array index)) fourZ
        array-start maximumArrayIndex) →
    ((index : Int) →
      let node = pointer-memory (shift array index)
      in
      item ≠ node →
      start-index ≤Z index →
      index <Z upper →
      Separated item fourZ node fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      start-index ≤Z right-index →
      start-index ≤Z left-index →
      right-index <Z upper →
      left-index <Z upper →
      pointer-memory (shift array left-index) ≠
      pointer-memory (shift array right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      start-index ≤Z right-index →
      start-index ≤Z left-index →
      right-index <Z upper →
      left-index <Z upper →
      Separated
        (pointer-memory (shift array left-index)) fourZ
        (pointer-memory (shift array right-index)) fourZ) →
    havoc
      havoc-memory pointer-memory
      (shift array start-index)
      (subtractInt length oneZ) ≡ post-memory →
    PArraySwipeLeft
      post-memory
      pointer-memory
      array
      start-index
      (subtractInt upper oneZ) →
    PArraySwipeLeft
      (update post-memory head root-next)
      pointer-memory
      array
      selected-index
      (subtractInt upper oneZ)

list-remove-contains-item-post-swiped-part2-goal62 : Set₁
list-remove-contains-item-post-swiped-part2-goal62 =
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC62.goal62 region linked index-of-theory
