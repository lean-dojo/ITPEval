-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_push_Why3_ide_VClist_push_does_not_contain_item_post_Separation_2_part1_goal56:
-- the final list-push pointer-memory updates keep the four-byte node blocks
-- at two distinct in-range array indices separated, under the stated
-- linked-list, integer-bound, memory-validity, separation, framing,
-- unchanged-region, and pointer-distinctness assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module ListPushDoesNotContainItemPostSeparation2Part1Goal56 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int)
open import ListAddFinalAddPreLinked2Part1Goal43

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

module VC56
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal56 : Set
  goal56 =
    (i i1 : Int) →
    (t3 : Addr → Addr) →
    (a3 a4 a2 : Addr) →
    (t2 : Addr → Addr) →
    (a a1 : Addr) →
    (i3 i2 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    (t4 : Addr → Addr) →
    let
      x = subtractInt i oneZ
      x1 = subtractInt (addInt i i1) oneZ
      x2 = lIndexOf t3 a3 a4 x x1
      x3 = addInt oneZ x2
      x4 = addInt i i1
      a5 = shift a4 zeroZ
      a6 = t3 a2
      a7 = shift a4 x
      a8 =
        havoc
          t2
          (update
            (update t3 a2 a)
            (shift
              (t3 (shift a4 (subtractInt x2 oneZ)))
              zeroZ)
            a1)
          (shift a4 x2)
          (subtractInt x1 x2)
      a9 = a8 a2
      a13 =
        havoc
          t4
          a8
          (shift a4 x)
          (addInt oneZ i1)
      a10 =
        update
          (update a13 (shift a3 zeroZ) a9)
          a7
          a3
      a11 = update a10 a2 a3
    in
    i3 ≠ i2 →
    addr zeroZ zeroZ ≠ a3 →
    x3 ≡ x4 →
    zeroZ <Z i →
    zeroZ ≤Z i1 →
    i2 <Z x4 →
    i3 <Z x4 →
    region (Addr.base a2) ≤Z zeroZ →
    region (Addr.base a3) ≤Z zeroZ →
    region (Addr.base a4) ≤Z zeroZ →
    x2 <Z x4 →
    i1 ≤Z maximumArrayIndexMinusOne →
    x4 ≤Z maximumArrayIndex →
    i ≤Z addInt oneZ i2 →
    i ≤Z addInt oneZ i3 →
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
      t3 (shift a4 index) ≠ a3) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      IsSint32 index →
      t3 (shift a4 index) ≠ a3) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        a2 oneZ
        (t3 (shift a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        (t3 (shift a4 index)) fourZ
        a5 maximumArrayIndex) →
    ((index : Int) →
      let node = t3 (shift a4 index)
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
      t3 (shift a4 left-index) ≠
      t3 (shift a4 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      Separated
        (t3 (shift a4 left-index)) fourZ
        (t3 (shift a4 right-index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      a8 (shift a4 index) ≠ a3) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        a2 oneZ
        (a8 (shift a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        a3 fourZ
        (a8 (shift a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z addInt oneZ index →
      addInt twoZ index ≤Z x4 →
      Separated
        (a8 (shift a4 index)) fourZ
        a5 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      a8 (shift a4 left-index) ≠
      a8 (shift a4 right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z addInt oneZ right-index →
      i ≤Z addInt oneZ left-index →
      addInt twoZ right-index ≤Z x4 →
      addInt twoZ left-index ≤Z x4 →
      Separated
        (a8 (shift a4 left-index)) fourZ
        (a8 (shift a4 right-index)) fourZ) →
    a13 a2 ≡ a9 →
    Separated
      (a13 a2) fourZ
      a5 maximumArrayIndex →
    ((index : Int) →
      i ≤Z index →
      index <Z x4 →
      Separated
        a2 oneZ
        (a13 (shift a4 index)) fourZ) →
    ((index : Int) →
      i ≤Z index →
      index <Z x4 →
      Separated
        (a13 (shift a4 index)) fourZ
        a5 maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i ≤Z right-index →
      i ≤Z left-index →
      right-index <Z x4 →
      left-index <Z x4 →
      Separated
        (a13 (shift a4 left-index)) fourZ
        (a13 (shift a4 right-index)) fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      x ≤Z right-index →
      x ≤Z left-index →
      right-index <Z x4 →
      left-index <Z x4 →
      a13 (shift a4 left-index) ≠
      a13 (shift a4 right-index)) →
    PArraySwipeRight a13 a8 a4 i x4 →
    PLinkedN
      allocation a13 a9 a4 i i1
      (addr zeroZ zeroZ) →
    Separated
      (a11 (shift a4 i3)) fourZ
      (a11 (shift a4 i2)) fourZ

list-push-does-not-contain-item-post-separation-2-part1-goal56 : Set₂
list-push-does-not-contain-item-post-separation-2-part1-goal56 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC56.goal56 {R} region linked index-of-theory
