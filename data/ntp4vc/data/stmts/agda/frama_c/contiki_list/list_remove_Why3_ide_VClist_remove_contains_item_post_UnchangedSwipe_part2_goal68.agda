-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part2_goal68:
-- the list-removal verification condition states that after updating the
-- head pointer to its successor, the array entry at the given index
-- loads the same list-node structure as the following array entry did in the
-- original memory, under the stated integer bounds, memory validity, framing,
-- linked-list, separation, index-of, and pointer-distinctness assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListRemoveContainsItemPostUnchangedSwipePart2Goal68 where

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

module VC68
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal68 : Set
  goal68 =
    (pointer-memory : Addr → Addr) →
    (post-memory havoc-memory : Addr → Addr) →
    (head array : Addr) →
    (i2 i i1 i3 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      first-node = pointer-memory head
      selected-node = pointer-memory (shift array i2)
      upper = addInt i i1
      selected-index =
        lIndexOf pointer-memory selected-node array i1 upper
      array-start = shift array zeroZ
      updated-pointer-memory =
        update
          post-memory
          head
          (pointer-memory (shift first-node zeroZ))
    in
    first-node ≠ addr zeroZ zeroZ →
    selected-node ≠ addr zeroZ zeroZ →
    selected-node ≡ first-node →
    zeroZ ≤Z i →
    zeroZ ≤Z i1 →
    i1 ≤Z i2 →
    i2 <Z upper →
    region (Addr.base head) ≤Z zeroZ →
    region (Addr.base array) ≤Z zeroZ →
    region (Addr.base first-node) ≤Z zeroZ →
    selected-index ≤Z i3 →
    i ≤Z maximumArrayIndexMinusOne →
    addInt twoZ i3 ≤Z upper →
    Framed pointer-memory →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    ValidRW allocation head oneZ →
    ValidRW allocation array-start maximumArrayIndex →
    Separated head oneZ array-start maximumArrayIndex →
    Separated first-node fourZ array-start maximumArrayIndex →
    PLinkedN
      allocation pointer-memory first-node array i1 i
      (addr zeroZ zeroZ) →
    IsSint32 selected-index →
    ((index : Int) →
      i1 ≤Z index →
      index <Z upper →
      Separated
        head oneZ
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
      (shift array i1)
      (subtractInt i oneZ) ≡
      post-memory →
    PArraySwipeLeft
      post-memory pointer-memory
      array i1 (subtractInt upper oneZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z subtractInt upper oneZ →
      Separated
        head oneZ
        (post-memory (shift array index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z subtractInt upper oneZ →
      Separated
        (post-memory (shift array index)) fourZ
        array-start maximumArrayIndex) →
    EqS1List
      (loadS1List
        (updated-pointer-memory (shift array i3))
        float-memory
        updated-pointer-memory)
      (loadS1List
        (pointer-memory (shift array (addInt oneZ i3)))
        float-memory
        pointer-memory)

list-remove-contains-item-post-unchanged-swipe-part2-goal68 : Set₂
list-remove-contains-item-post-unchanged-swipe-part2-goal68 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC68.goal68 {R} region linked index-of-theory
