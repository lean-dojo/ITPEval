-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_push_Why3_ide_VClist_push_contains_item_post_3_part4_goal33:
-- the final list-push pointer-memory update realizes the required rightward
-- array swipe through the located item, under the stated linked-list,
-- integer-bound, memory-validity, separation, framing, and update assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListPushContainsItemPost3Part4Goal33 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int; negsuc; pos)
open import Agda.Builtin.Nat using (zero)
open import ListAddFinalAddPreLinked2Part1Goal43

maximumArrayIndexMinusTwo minusOneZ : Int
maximumArrayIndexMinusTwo = pos 2147483644
minusOneZ = negsuc zero

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
  pointer-memory1 (shift array (addInt oneZ index)) ≡
  pointer-memory0 (shift array index)

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
  pointer-memory1 (shift array (subtractInt index oneZ)) ≡
  pointer-memory0 (shift array index)

module VC33
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal33 : Set
  goal33 =
    (t3 : Addr → Addr) →
    (a3 : Addr) →
    (i3 i2 i1 i : Int) →
    (a2 : Addr) →
    (t2 : Addr → Addr) →
    (a a1 : Addr) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    (t4 : Addr → Addr) →
    let
      a4 = t3 (shift a3 i3)
      a5 = t3 (shift a3 i2)
      x = subtractInt i1 oneZ
      x1 = addInt i i1
      x2 = lIndexOf t3 a4 a3 x x1
      x3 = lIndexOf t3 a5 a3 x x1
      x4 = addInt oneZ i
      a6 = shift a3 zeroZ
      a7 = t3 a2
      a8 = shift a3 x
      x5 = subtractInt x2 oneZ
      a9 = shift a3 x5
      a10 = t3 a9
      a11 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift a10 zeroZ)
            a1)
          (shift a3 x2)
          (subtractInt (addInt i i1) x2)
      a12 = a11 a2
      a16 =
        havoc
          t4
          a11
          (shift a3 x)
          x4
      a13 =
        update
          (update a16 (shift a4 zeroZ) a12)
          a8
          a4
      a14 = update a13 a2 a4
      item-occurs =
        Exists Int
          (λ index →
            (a4 ≡ t3 (shift a3 index)) ∧
            (index <Z x1) ∧
            (i1 ≤Z addInt oneZ index))
      item-absent =
        (index : Int) →
        index <Z x1 →
        i1 ≤Z addInt oneZ index →
        a4 ≠ t3 (shift a3 index)
    in
    a4 ≠ addr zeroZ zeroZ →
    a4 ≡ a5 →
    x2 ≡ x3 →
    x1 ≠ x2 →
    zeroZ <Z i1 →
    i2 <Z x1 →
    i3 <Z x1 →
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
    i1 ≤Z addInt oneZ x2 →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation a2 oneZ →
    IsSint32 x →
    IsSint32 x4 →
    ValidRW allocation a6 maximumArrayIndex →
    ValidRW allocation a5 fourZ →
    Separated a2 oneZ a6 maximumArrayIndex →
    Separated a7 fourZ a6 maximumArrayIndex →
    Separated a2 oneZ a5 fourZ →
    Separated a5 fourZ a6 maximumArrayIndex →
    ValidRW allocation a8 x4 →
    PLinkedN
      allocation t3 a7 a3 x x4
      (addr zeroZ zeroZ) →
    IsSint32 x3 →
    IsSint32 x2 →
    Separated a12 fourZ a6 maximumArrayIndex →
    EqS1List
      (loadS1List a4 float-memory a11)
      (loadS1List a4 float-memory t3) →
    PUnchanged
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
      a11 (shift a3 index) ≠ a4) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      a11 (shift a3 index) ≠ a4) →
    (item-occurs →
      PLinkedN
        allocation a11 a12 a3 x i
        (addr zeroZ zeroZ)) →
    (item-absent →
      PLinkedN
        allocation a11 a12 a3 x x4
        (addr zeroZ zeroZ)) →
    (item-absent →
      PUnchanged
        allocation a11 float-memory
        allocation t3 float-memory
        a3 x x1) →
    (item-occurs →
      PUnchanged
        allocation a11 float-memory
        allocation t3 float-memory
        a3 x x5) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        a2 oneZ
        (a11 (shift a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      Separated
        a2 oneZ
        (a11 (shift a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        a4 fourZ
        (a11 (shift a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      Separated
        a4 fourZ
        (a11 (shift a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        (a11 (shift a3 index)) fourZ
        a6 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x1 →
      Separated
        (a11 (shift a3 index)) fourZ
        a6 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      x2 ≤Z index →
      addInt twoZ index ≤Z x1 →
      EqS1List
        (loadS1List
          (a11 (shift a3 index))
          float-memory
          a11)
        (loadS1List
          (t3 (shift a3 (addInt oneZ index)))
          float-memory
          t3)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      a11 (shift a3 left-index) ≠
      a11 (shift a3 right-index)) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x1 →
      addInt twoZ left-index ≤Z x1 →
      a11 (shift a3 left-index) ≠
      a11 (shift a3 right-index)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      Separated
        (a11 (shift a3 left-index)) fourZ
        (a11 (shift a3 right-index)) fourZ) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x1 →
      addInt twoZ left-index ≤Z x1 →
      Separated
        (a11 (shift a3 left-index)) fourZ
        (a11 (shift a3 right-index)) fourZ) →
    ((index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        a2 oneZ
        (t3 (shift a3 index)) fourZ) →
    ((index : Int) →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated
        (t3 (shift a3 index)) fourZ
        a6 maximumArrayIndex) →
    ((index : Int) →
      let node = t3 (shift a3 index)
      in
      a5 ≠ node →
      index <Z x1 →
      i1 ≤Z addInt oneZ index →
      Separated a5 fourZ node fourZ) →
    ((index : Int) →
      let node = t3 (shift a3 index)
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
      t3 (shift a3 left-index) ≠
      t3 (shift a3 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x1 →
      left-index <Z x1 →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      Separated
        (t3 (shift a3 left-index)) fourZ
        (t3 (shift a3 right-index)) fourZ) →
    a16 a2 ≡ a12 →
    Separated
      (a16 a2) fourZ
      a6 maximumArrayIndex →
    ((index : Int) →
      i1 ≤Z index →
      index <Z x1 →
      Separated
        a2 oneZ
        (a16 (shift a3 index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z x1 →
      Separated
        (a16 (shift a3 index)) fourZ
        a6 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z x1 →
      left-index <Z x1 →
      Separated
        (a16 (shift a3 left-index)) fourZ
        (a16 (shift a3 right-index)) fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      x ≤Z right-index →
      x ≤Z left-index →
      right-index <Z x1 →
      left-index <Z x1 →
      a16 (shift a3 left-index) ≠
      a16 (shift a3 right-index)) →
    PArraySwipeRight a16 a11 a3 i1 x1 →
    PLinkedN
      allocation a16 a12 a3 i1 i
      (addr zeroZ zeroZ) →
    PArraySwipeRight
      a14 t3 a3 i1 (addInt oneZ x3)

list-push-contains-item-post-3-part4-goal33 : Set₂
list-push-contains-item-post-3-part4-goal33 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC33.goal33 {R} region linked index-of-theory
