-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_GhostSeparation_part4_goal37:
-- the two-stage havoc and nested pointer-memory updates keep the designated
-- list-cell address separated from the updated pointer-array entry, with
-- pointer indices scaled by eight bytes and raw shifts retained for fields,
-- under the stated linked-list, validity, separation, framing, and swipe assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListPushContainsItemPostGhostSeparationPart4Goal37 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (zero)
open import ListAddFinalAddPreLinked2Part1Goal43

maximumArrayIndexMinusTwo minusOneZ : Int
maximumArrayIndexMinusTwo = pos 2147483644
minusOneZ = negsuc zero

scaleByEight : Int → Int
scaleByEight k =
  let
    twice = addInt k k
    four-times = addInt twice twice
  in
  addInt four-times four-times

shiftPtr : Addr → Int → Addr
shiftPtr p k = shift p k

PArraySwipeLeft :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
PArraySwipeLeft
  pointer-memory0 pointer-memory1 array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  pointer-memory1 (shiftPtr array (addInt oneZ index)) ≡
  pointer-memory0 (shiftPtr array index)

PArraySwipeRight :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
PArraySwipeRight
  pointer-memory0 pointer-memory1 array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  pointer-memory1 (shiftPtr array (subtractInt index oneZ)) ≡
  pointer-memory0 (shiftPtr array index)

record PointerIndexOfTheory : Set where
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
      pointer-memory (shiftPtr array down) ≡ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf pointer-memory item array down up ≡ down

    not-the-item :
      (pointer-memory : Addr → Addr) →
      (array : Addr) →
      (down : Int) →
      (item : Addr) →
      (up : Int) →
      pointer-memory (shiftPtr array down) ≠ item →
      zeroZ ≤Z down →
      down <Z up →
      lIndexOf
        pointer-memory item array (addInt oneZ down) up ≡
      lIndexOf pointer-memory item array down up

data PLinkedNPtr :
  (Int → Int) →
  (Addr → Addr) →
  Addr →
  Addr →
  Int →
  Int →
  Addr →
  Set where

  linked-ptr-bound :
    (index : Int) →
    (allocation : Int → Int) →
    (pointer-memory : Addr → Addr) →
    (bound array : Addr) →
    zeroZ ≤Z index →
    index ≤Z maximumArrayIndex →
    PLinkedNPtr
      allocation pointer-memory bound array index zeroZ bound

  linked-ptr-cons :
    (index n : Int) →
    (pointer-memory : Addr → Addr) →
    (array root : Addr) →
    (allocation : Int → Int) →
    (bound : Addr) →
    pointer-memory (shiftPtr array index) ≡ root →
    zeroZ <Z n →
    zeroZ ≤Z index →
    zeroZ ≤Z addInt index n →
    addInt index n ≤Z maximumArrayIndex →
    ValidRW allocation root fourZ →
    PLinkedNPtr
      allocation
      pointer-memory
      (pointer-memory (shift root zeroZ))
      array
      (addInt oneZ index)
      (subtractInt n oneZ)
      bound →
    PLinkedNPtr
      allocation pointer-memory root array index n bound

PUnchangedPtr :
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
PUnchangedPtr
  allocation0 pointer-memory0 float-memory0
  allocation1 pointer-memory1 float-memory1
  array down up =
  (index : Int) →
  let
    location = shiftPtr array index
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

module VC37
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : PointerIndexOfTheory) where

  open PointerIndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal37 : Set
  goal37 =
    (t3 : Addr → Addr) →
    (a3 : Addr) →
    (i3 i2 i1 i : Int) →
    (a2 : Addr) →
    (t2 : Addr → Addr) →
    (a a1 : Addr) →
    (i4 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    (t4 : Addr → Addr) →
    let
      a4 = t3 (shiftPtr a3 i3)
      a5 = t3 (shiftPtr a3 i2)
      x = subtractInt i1 oneZ
      x1 = addInt i i1
      x2 = lIndexOf t3 a4 a3 x x1
      x3 = addInt oneZ i
      a6 = shiftPtr a3 zeroZ
      a7 = t3 a2
      a8 = shiftPtr a3 x
      x4 = subtractInt x2 oneZ
      a9 = shiftPtr a3 x4
      a10 = t3 a9
      a11 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift a10 zeroZ)
            a1)
          (shiftPtr a3 x2)
          (subtractInt (addInt i i1) x2)
      a12 = a11 a2
      a16 =
        havoc
          t4
          a11
          (shiftPtr a3 x)
          x3
      a13 =
        update
          (update a16 (shift a4 zeroZ) a12)
          a8
          a4
      a14 = update a13 a2 a4
      item-occurs =
        Exists Int
          (λ index →
            (a4 ≡ t3 (shiftPtr a3 index)) ∧
            (index <Z x1) ∧
            (i1 ≤Z addInt oneZ index))
      item-absent =
        (index : Int) →
        index <Z x1 →
        i1 ≤Z addInt oneZ index →
        a4 ≠ t3 (shiftPtr a3 index)
    in
    a4 ≠ addr zeroZ zeroZ →
    a4 ≡ a5 →
    x2 ≡ lIndexOf t3 a5 a3 x x1 →
    x1 ≠ x2 →
    zeroZ <Z i1 →
    i2 <Z x1 →
    i3 <Z x1 →
    i4 <Z x1 →
    region (Addr.base a2) ≤Z zeroZ →
    region (Addr.base a3) ≤Z zeroZ →
    region (Addr.base a4) ≤Z zeroZ →
    x2 <Z x1 →
    x2 ≤Z x1 →
    minusOneZ ≤Z i →
    i ≤Z maximumArrayIndexMinusTwo →
    x1 ≤Z maximumArrayIndexMinusOne →
    i1 ≤Z addInt oneZ i2 →
    i1 ≤Z addInt oneZ i3 →
    i1 ≤Z addInt oneZ i4 →
    i1 ≤Z addInt oneZ x2 →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation a2 oneZ →
    IsSint32 x →
    IsSint32 x3 →
    ValidRW allocation a6 maximumArrayIndex →
    ValidRW allocation a5 fourZ →
    Separated a2 oneZ a6 maximumArrayIndex →
    Separated a7 fourZ a6 maximumArrayIndex →
    Separated a2 oneZ a5 fourZ →
    Separated a5 fourZ a6 maximumArrayIndex →
    ValidRW allocation a8 x3 →
    PLinkedNPtr
      allocation t3 a7 a3 x x3
      (addr zeroZ zeroZ) →
    IsSint32 x2 →
    Separated a12 fourZ a6 maximumArrayIndex →
    EqS1List
      (loadS1List a4 float-memory a11)
      (loadS1List a4 float-memory t3) →
    PUnchangedPtr
      allocation a14 float-memory
      allocation a13 float-memory
      a3 x x1 →
    (i1 ≤Z x2 →
      item-occurs →
      a11 a9 ≡ a10) →
    (item-occurs →
      PArraySwipeLeft
        a11 t3 a3 x2
        (subtractInt (addInt i i1) oneZ)) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      a11 (shiftPtr a3 index) ≠ a4) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      a11 (shiftPtr a3 index) ≠ a4) →
    (item-occurs →
      PLinkedNPtr
        allocation a11 a12 a3 x i
        (addr zeroZ zeroZ)) →
    (item-absent →
      PLinkedNPtr
        allocation a11 a12 a3 x x3
        (addr zeroZ zeroZ)) →
    (item-absent →
      PUnchangedPtr
        allocation a11 float-memory
        allocation t3 float-memory
        a3 x x1) →
    (item-occurs →
      PUnchangedPtr
        allocation a11 float-memory
        allocation t3 float-memory
        a3 x x4) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        a2 oneZ
        (a11 (shiftPtr a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      Separated
        a2 oneZ
        (a11 (shiftPtr a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        a4 fourZ
        (a11 (shiftPtr a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      Separated
        a4 fourZ
        (a11 (shiftPtr a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        (a11 (shiftPtr a3 index)) fourZ
        a6 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      Separated
        (a11 (shiftPtr a3 index)) fourZ
        a6 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      x2 ≤Z index →
      addInt twoZ index ≤Z x1 →
      EqS1List
        (loadS1List
          (a11 (shiftPtr a3 index))
          float-memory
          a11)
        (loadS1List
          (t3 (shiftPtr a3 (addInt oneZ index)))
          float-memory
          t3)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      a11 (shiftPtr a3 left-index) ≠
      a11 (shiftPtr a3 right-index)) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x1 →
      addInt twoZ left-index ≤Z x1 →
      a11 (shiftPtr a3 left-index) ≠
      a11 (shiftPtr a3 right-index)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      Separated
        (a11 (shiftPtr a3 left-index)) fourZ
        (a11 (shiftPtr a3 right-index)) fourZ) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x1 →
      addInt twoZ left-index ≤Z x1 →
      Separated
        (a11 (shiftPtr a3 left-index)) fourZ
        (a11 (shiftPtr a3 right-index)) fourZ) →
    ((index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        a2 oneZ
        (t3 (shiftPtr a3 index)) fourZ) →
    ((index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        (t3 (shiftPtr a3 index)) fourZ
        a6 maximumArrayIndex) →
    ((index : Int) →
      let node = t3 (shiftPtr a3 index)
      in
      a5 ≠ node →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated a5 fourZ node fourZ) →
    ((index : Int) →
      let node = t3 (shiftPtr a3 index)
      in
      a4 ≠ node →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated a4 fourZ node fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      t3 (shiftPtr a3 left-index) ≠
      t3 (shiftPtr a3 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      Separated
        (t3 (shiftPtr a3 left-index)) fourZ
        (t3 (shiftPtr a3 right-index)) fourZ) →
    a16 a2 ≡ a12 →
    Separated
      (a16 a2) fourZ
      a6 maximumArrayIndex →
    ((index : Int) →
      i1 ≤Z index →
      index <Z x1 →
      Separated
        a2 oneZ
        (a16 (shiftPtr a3 index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z x1 →
      Separated
        (a16 (shiftPtr a3 index)) fourZ
        a6 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z x1 →
      left-index <Z x1 →
      Separated
        (a16 (shiftPtr a3 left-index)) fourZ
        (a16 (shiftPtr a3 right-index)) fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      x ≤Z right-index →
      x ≤Z left-index →
      right-index <Z x1 →
      left-index <Z x1 →
      a16 (shiftPtr a3 left-index) ≠
      a16 (shiftPtr a3 right-index)) →
    PArraySwipeRight a16 a11 a3 i1 x1 →
    PLinkedNPtr
      allocation a16 a12 a3 i1 i
      (addr zeroZ zeroZ) →
    Separated
      a2 oneZ
      (a14 (shiftPtr a3 i4)) fourZ

list-push-contains-item-post-ghost-separation-part4-goal37 : Set₂
list-push-contains-item-post-ghost-separation-part4-goal37 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : PointerIndexOfTheory) →
  VC37.goal37 {R} region linked index-of-theory
