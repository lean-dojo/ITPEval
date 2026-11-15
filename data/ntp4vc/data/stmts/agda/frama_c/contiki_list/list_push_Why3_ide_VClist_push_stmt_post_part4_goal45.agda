-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_push_Why3_ide_VClist_push_stmt_post_part4_goal45:
-- the final list-push pointer-memory update preserves the specified array
-- segment, under the stated integer bounds, linked-list, memory-validity,
-- separation, framing, index-search, and case-split assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListPushStmtPostPart4Goal45 where

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

module VC45
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal45 : Set
  goal45 =
    (t3 : Addr → Addr) →
    (a3 : Addr) →
    (i2 i i1 : Int) →
    (a2 : Addr) →
    (t2 : Addr → Addr) →
    (a a1 : Addr) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    (t4 : Addr → Addr) →
    let
      a4 = t3 (shift a3 i2)
      x = addInt i i1
      x1 = subtractInt i1 oneZ
      x2 = lIndexOf t3 a4 a3 x1 x
      x3 = addInt oneZ i
      a5 = shift a3 zeroZ
      a6 = t3 a2
      a7 = shift a3 x1
      x4 = subtractInt x2 oneZ
      a8 = shift a3 x4
      a9 = t3 a8
      a10 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift a9 zeroZ)
            a1)
          (shift a3 x2)
          (subtractInt (addInt i i1) x2)
      a11 = a10 a2
      a14 =
        havoc
          t4
          a10
          (shift a3 x1)
          (addInt oneZ i)
      a12 =
        update
          (update a14 (shift a4 zeroZ) a11)
          a7
          a4
      item-occurs =
        Exists Int
          (λ index →
            (a4 ≡ t3 (shift a3 index)) ∧
            (index <Z x) ∧
            (i1 ≤Z addInt oneZ index))
      item-absent =
        (index : Int) →
        index <Z x →
        i1 ≤Z addInt oneZ index →
        a4 ≠ t3 (shift a3 index)
    in
    a4 ≠ addr zeroZ zeroZ →
    x ≠ x2 →
    zeroZ <Z i1 →
    i2 <Z x →
    region (Addr.base a2) ≤Z zeroZ →
    region (Addr.base a3) ≤Z zeroZ →
    region (Addr.base a4) ≤Z zeroZ →
    x2 <Z x →
    x2 ≤Z x →
    minusOneZ ≤Z i →
    i ≤Z maximumArrayIndexMinusTwo →
    x ≤Z maximumArrayIndexMinusOne →
    i1 ≤Z addInt oneZ i2 →
    i1 ≤Z addInt oneZ x2 →
    Framed t3 →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation a2 oneZ →
    IsSint32 x1 →
    IsSint32 x3 →
    ValidRW allocation a5 maximumArrayIndex →
    ValidRW allocation a4 fourZ →
    Separated a2 oneZ a5 maximumArrayIndex →
    Separated a6 fourZ a5 maximumArrayIndex →
    Separated a2 oneZ a4 fourZ →
    Separated a4 fourZ a5 maximumArrayIndex →
    ValidRW allocation a7 x3 →
    PLinkedN
      allocation t3 a6 a3 x1 x3
      (addr zeroZ zeroZ) →
    IsSint32 x2 →
    Separated a11 fourZ a5 maximumArrayIndex →
    EqS1List
      (loadS1List a4 float-memory a10)
      (loadS1List a4 float-memory t3) →
    (i1 ≤Z x2 →
      item-occurs →
      a10 a8 ≡ a9) →
    (item-occurs →
      PArraySwipeLeft
        a10 t3 a3 x2
        (subtractInt (addInt i i1) oneZ)) →
    (item-absent →
      (index : Int) →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      a10 (shift a3 index) ≠ a4) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x →
      a10 (shift a3 index) ≠ a4) →
    (item-occurs →
      PLinkedN
        allocation a10 a11 a3 x1 i
        (addr zeroZ zeroZ)) →
    (item-absent →
      PLinkedN
        allocation a10 a11 a3 x1 x3
        (addr zeroZ zeroZ)) →
    (item-absent →
      PUnchanged
        allocation a10 float-memory
        allocation t3 float-memory
        a3 x1 x) →
    (item-occurs →
      PUnchanged
        allocation a10 float-memory
        allocation t3 float-memory
        a3 x1 x4) →
    (item-absent →
      (index : Int) →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      Separated
        a2 oneZ
        (a10 (shift a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x →
      Separated
        a2 oneZ
        (a10 (shift a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      Separated
        a4 fourZ
        (a10 (shift a3 index)) fourZ) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x →
      Separated
        a4 fourZ
        (a10 (shift a3 index)) fourZ) →
    (item-absent →
      (index : Int) →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      Separated
        (a10 (shift a3 index)) fourZ
        a5 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      i1 ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x →
      Separated
        (a10 (shift a3 index)) fourZ
        a5 maximumArrayIndex) →
    (item-occurs →
      (index : Int) →
      x2 ≤Z index →
      addInt twoZ index ≤Z x →
      EqS1List
        (loadS1List
          (a10 (shift a3 index))
          float-memory
          a10)
        (loadS1List
          (t3 (shift a3 (addInt oneZ index)))
          float-memory
          t3)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x →
      left-index <Z x →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      a10 (shift a3 left-index) ≠
      a10 (shift a3 right-index)) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x →
      addInt twoZ left-index ≤Z x →
      a10 (shift a3 left-index) ≠
      a10 (shift a3 right-index)) →
    (item-absent →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x →
      left-index <Z x →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      Separated
        (a10 (shift a3 left-index)) fourZ
        (a10 (shift a3 right-index)) fourZ) →
    (item-occurs →
      (left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x →
      addInt twoZ left-index ≤Z x →
      Separated
        (a10 (shift a3 left-index)) fourZ
        (a10 (shift a3 right-index)) fourZ) →
    ((index : Int) →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      Separated
        a2 oneZ
        (t3 (shift a3 index)) fourZ) →
    ((index : Int) →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      Separated
        (t3 (shift a3 index)) fourZ
        a5 maximumArrayIndex) →
    ((index : Int) →
      let node = t3 (shift a3 index)
      in
      a4 ≠ node →
      index <Z x →
      i1 ≤Z addInt oneZ index →
      Separated a4 fourZ node fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x →
      left-index <Z x →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      t3 (shift a3 left-index) ≠
      t3 (shift a3 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      right-index <Z x →
      left-index <Z x →
      i1 ≤Z addInt oneZ right-index →
      i1 ≤Z addInt oneZ left-index →
      Separated
        (t3 (shift a3 left-index)) fourZ
        (t3 (shift a3 right-index)) fourZ) →
    a14 a2 ≡ a11 →
    Separated
      (a14 a2) fourZ
      a5 maximumArrayIndex →
    ((index : Int) →
      i1 ≤Z index →
      index <Z x →
      Separated
        a2 oneZ
        (a14 (shift a3 index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z x →
      Separated
        (a14 (shift a3 index)) fourZ
        a5 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z x →
      left-index <Z x →
      Separated
        (a14 (shift a3 left-index)) fourZ
        (a14 (shift a3 right-index)) fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      x1 ≤Z right-index →
      x1 ≤Z left-index →
      right-index <Z x →
      left-index <Z x →
      a14 (shift a3 left-index) ≠
      a14 (shift a3 right-index)) →
    PArraySwipeRight a14 a10 a3 i1 x →
    PLinkedN
      allocation a14 a11 a3 i1 i
      (addr zeroZ zeroZ) →
    PUnchanged
      allocation (update a12 a2 a4) float-memory
      allocation a12 float-memory
      a3 x1 x

list-push-stmt-post-part4-goal45 : Set₂
list-push-stmt-post-part4-goal45 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC45.goal45 {R} region linked index-of-theory
