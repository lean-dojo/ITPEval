-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_Swiped_part5_goal64:
-- the list-removal verification condition states that updating the current
-- node's next pointer makes the array segment from the selected-item index
-- through the penultimate occupied slot a left swipe, under the stated
-- integer bounds, memory validity, framing, linked-list, unchanged-memory,
-- separation, index-of, and pointer-distinctness assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListRemoveContainsItemPostSwipedPart5Goal64 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int)
open import ListAddFinalAddPreLinked2Part1Goal43

PArraySwipeLeft :
  (Addr → Addr) →
  (Addr → Addr) →
  Addr →
  Int →
  Int →
  Set
PArraySwipeLeft updated-memory original-memory array down up =
  (index : Int) →
  down ≤Z index →
  index <Z up →
  original-memory (shift array (addInt oneZ index)) ≡
  updated-memory (shift array index)

module VC64
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal64 : Set
  goal64 =
    (pointer-memory : Addr → Addr) →
    (post-memory havoc-memory : Addr → Addr) →
    (head current array : Addr) →
    (i2 i i1 i3 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      first-node = pointer-memory head
      current-slot = shift current zeroZ
      current-node = pointer-memory current-slot
      selected-node = pointer-memory (shift array i2)
      upper = addInt i i1
      array-start = shift array zeroZ
      selected-index =
        lIndexOf pointer-memory selected-node array i1 upper
      updated-pointer-memory =
        update
          post-memory
          current-slot
          (pointer-memory (shift current-node zeroZ))
    in
    first-node ≠ addr zeroZ zeroZ →
    current-node ≠ first-node →
    selected-node ≠ addr zeroZ zeroZ →
    selected-node ≡ current-node →
    zeroZ ≤Z i →
    zeroZ ≤Z i1 →
    i1 ≤Z i2 →
    i1 ≤Z i3 →
    i2 <Z upper →
    i3 ≤Z upper →
    region (Addr.base head) ≤Z zeroZ →
    region (Addr.base array) ≤Z zeroZ →
    region (Addr.base current-node) ≤Z zeroZ →
    i ≤Z maximumArrayIndexMinusOne →
    Framed pointer-memory →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    IsSint32 i3 →
    ValidRW allocation head oneZ →
    ValidRW allocation array-start maximumArrayIndex →
    Separated head oneZ array-start maximumArrayIndex →
    Separated first-node fourZ array-start maximumArrayIndex →
    PLinkedN
      allocation pointer-memory first-node array i1 i
      (addr zeroZ zeroZ) →
    PUnchanged
      allocation pointer-memory float-memory
      allocation pointer-memory float-memory
      array i1 i3 →
    PLinkedN
      allocation pointer-memory current array i3 oneZ
      current-node →
    IsSint32 selected-index →
    PLinkedN
      allocation pointer-memory first-node array i1
      (subtractInt i3 i1) current →
    PLinkedN
      allocation pointer-memory current-node array
      (addInt oneZ i3)
      (subtractInt (subtractInt upper oneZ) i3)
      (addr zeroZ zeroZ) →
    ((index : Int) →
      i1 ≤Z index →
      index ≤Z i3 →
      pointer-memory (shift array index) ≠ current-node) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z upper →
      Separated
        head oneZ
        (pointer-memory (shift array index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z i3 →
      Separated
        current-node fourZ
        (pointer-memory (shift array index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z upper →
      Separated
        (pointer-memory (shift array index)) fourZ
        array-start maximumArrayIndex) →
    ((index : Int) →
      let node = pointer-memory (shift array index)
      in
      selected-node ≠ node →
      i1 ≤Z index →
      index <Z upper →
      Separated selected-node fourZ node fourZ) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z upper →
      left-index <Z upper →
      pointer-memory (shift array left-index) ≠
      pointer-memory (shift array right-index)) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z upper →
      left-index <Z upper →
      Separated
        (pointer-memory (shift array left-index)) fourZ
        (pointer-memory (shift array right-index)) fourZ) →
    havoc
      havoc-memory pointer-memory
      (shift array (addInt oneZ i3))
      (subtractInt (subtractInt upper twoZ) i3) ≡
      post-memory →
    PArraySwipeLeft
      post-memory
      pointer-memory
      array
      (addInt oneZ i3)
      (subtractInt upper oneZ) →
    PArraySwipeLeft
      updated-pointer-memory
      pointer-memory
      array
      selected-index
      (subtractInt upper oneZ)

list-remove-contains-item-post-swiped-part5-goal64 : Set₂
list-remove-contains-item-post-swiped-part5-goal64 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC64.goal64 {R} region linked index-of-theory
