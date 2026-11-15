-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_add_Why3_ide_VClist_add_call_list_final_add_pre_Separation_2_part4_goal54:
-- the final list-add pointer-memory updates keep the node blocks at two
-- distinct in-range indices separated under the stated linked-list, memory,
-- framing, unchanged-region, array-shift, and pointer-distinctness assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListAddFinalAddPreSeparation2Part4Goal54 where

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
    (t3 : Addr → Addr) →
    (a3 : Addr) →
    (i2 i i1 : Int) →
    (t2 : Addr → Addr) →
    (a2 a a1 : Addr) →
    (i4 i3 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      a4 = t3 (shift a3 i2)
      x = addInt (addInt oneZ i) i1
      x1 = lIndexOf t3 a4 a3 i1 x
      x2 = subtractInt x1 oneZ
      a5 = shift a3 x2
      a6 = t3 a5
      a7 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift a6 zeroZ)
            a1)
          (shift a3 x1)
          (subtractInt (addInt (addInt oneZ i) i1) x1)
      a8 =
        update
          a7
          (shift a4 zeroZ)
          (addr zeroZ zeroZ)
      a9 = a8 a2
      final-index = subtractInt (addInt i i1) oneZ
      a10 = a8 (shift a3 final-index)
      total = addInt i i1
      count = addInt oneZ i
      a11 = shift a3 zeroZ
      a12 = t3 a2
      a13 = a7 a2
      item-occurs =
        Exists Int
          (λ index →
            (a4 ≡ t3 (shift a3 index)) ∧
            (i1 ≤Z index) ∧
            (index ≤Z total))
      item-absent =
        (index : Int) →
        i1 ≤Z index →
        index ≤Z total →
        a4 ≠ t3 (shift a3 index)
    in
    i4 ≠ i3 →
    a4 ≠ addr zeroZ zeroZ →
    x ≠ x1 →
    a9 ≠ addr zeroZ zeroZ →
    a10 ≠ addr zeroZ zeroZ →
    zeroZ ≤Z i1 →
    i1 ≤Z i2 →
    i1 ≤Z i3 →
    i1 ≤Z i4 →
    i3 <Z total →
    i4 <Z total →
    i2 ≤Z total →
    region (Addr.base a2) ≤Z zeroZ →
    region (Addr.base a3) ≤Z zeroZ →
    region (Addr.base a4) ≤Z zeroZ →
    i1 ≤Z x1 →
    x1 ≤Z total →
    minusOneZ ≤Z i →
    i ≤Z maximumArrayIndexMinusTwo →
    i1 ≤Z maximumArrayIndexMinusOne →
    total ≤Z maximumArrayIndexMinusTwo →
    x1 ≤Z x →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation a2 oneZ →
    IsSint32 count →
    ValidRW allocation a11 maximumArrayIndex →
    ValidRW allocation (shift a3 i1) count →
    ValidRW allocation a4 fourZ →
    Separated a2 oneZ a11 maximumArrayIndex →
    Separated a12 fourZ a11 maximumArrayIndex →
    Separated a2 oneZ a4 fourZ →
    Separated a4 fourZ a11 maximumArrayIndex →
    PLinkedN
      allocation t3 a12 a3 i1 count
      (addr zeroZ zeroZ) →
    IsSint32 x1 →
    Separated a13 fourZ a11 maximumArrayIndex →
    EqS1List
      (loadS1List a4 float-memory a7)
      (loadS1List a4 float-memory t3) →
    PLinkedN
      allocation a8 a9 a3 i1 i
      (addr zeroZ zeroZ) →
    PLinkedN
      allocation a8 a9 a3 i1
      (subtractInt i oneZ) a10 →
    (i1 <Z x1 →
      item-occurs →
      a7 a5 ≡ a6) →
    (item-occurs →
      PArraySwipeLeft a7 t3 a3 x1 total) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z index →
      index <Z total →
      a7 (shift a3 index) ≠ a4) →
    (item-absent →
      (index : Int) →
      i1 ≤Z index →
      index ≤Z total →
      a7 (shift a3 index) ≠ a4) →
    (item-occurs →
      PLinkedN
        allocation a7 a13 a3 i1 i
        (addr zeroZ zeroZ)) →
    (item-absent →
      PLinkedN
        allocation a7 a13 a3 i1 count
        (addr zeroZ zeroZ)) →
    (item-absent →
      PUnchanged
        allocation a7 float-memory
        allocation t3 float-memory
        a3 i1 x) →
    (item-occurs →
      PUnchanged
        allocation a7 float-memory
        allocation t3 float-memory
        a3 i1 x2) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z index →
      index <Z total →
      Separated
        a2 oneZ
        (a7 (shift a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      i1 ≤Z index →
      index ≤Z total →
      Separated
        a2 oneZ
        (a7 (shift a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z index →
      index <Z total →
      Separated
        a4 fourZ
        (a7 (shift a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      i1 ≤Z index →
      index ≤Z total →
      Separated
        a4 fourZ
        (a7 (shift a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z index →
      index <Z total →
      Separated
        (a7 (shift a3 index)) fourZ
        a11 maximumArrayIndex) →
    (item-absent →
      (index : Int) →
      i1 ≤Z index →
      index ≤Z total →
      Separated
        (a7 (shift a3 index)) fourZ
        a11 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      index <Z total →
      x1 ≤Z index →
      EqS1List
        (loadS1List
          (a7 (shift a3 index))
          float-memory
          a7)
        (loadS1List
          (t3 (shift a3 (addInt oneZ index)))
          float-memory
          t3)) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z total →
      left-index <Z total →
      a7 (shift a3 left-index) ≠
      a7 (shift a3 right-index)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index ≤Z total →
      left-index ≤Z total →
      a7 (shift a3 left-index) ≠
      a7 (shift a3 right-index)) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z total →
      left-index <Z total →
      Separated
        (a7 (shift a3 left-index)) fourZ
        (a7 (shift a3 right-index)) fourZ) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index ≤Z total →
      left-index ≤Z total →
      Separated
        (a7 (shift a3 left-index)) fourZ
        (a7 (shift a3 right-index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index ≤Z total →
      Separated
        a2 oneZ
        (t3 (shift a3 index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index ≤Z total →
      Separated
        (t3 (shift a3 index)) fourZ
        a11 maximumArrayIndex) →
    ((index : Int) →
      let node = t3 (shift a3 index)
      in
      a4 ≠ node →
      i1 ≤Z index →
      index ≤Z total →
      Separated a4 fourZ node fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index ≤Z total →
      left-index ≤Z total →
      t3 (shift a3 left-index) ≠
      t3 (shift a3 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index ≤Z total →
      left-index ≤Z total →
      Separated
        (t3 (shift a3 left-index)) fourZ
        (t3 (shift a3 right-index)) fourZ) →
    Separated
      (a8 (shift a3 i4)) fourZ
      (a8 (shift a3 i3)) fourZ

list-add-final-add-pre-separation-2-part4-goal54 : Set₂
list-add-final-add-pre-separation-2-part4-goal54 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC54.goal54 {R} region linked index-of-theory
