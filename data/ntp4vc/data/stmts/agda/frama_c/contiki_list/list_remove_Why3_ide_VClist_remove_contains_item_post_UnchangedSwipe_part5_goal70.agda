-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_contains_item_post_UnchangedSwipe_part5_goal70:
-- the list-removal verification condition states that after updating the
-- current node's next pointer, the array entry at the designated index loads
-- the same list-node structure as the following array entry did in the
-- original memory, under the stated integer bounds, memory validity, framing,
-- linked-list, unchanged-memory, separation, index-of, and pointer-distinctness
-- assumptions. This file contains no proof.

{-# OPTIONS --safe #-}

module ListRemoveContainsItemPostUnchangedSwipePart5Goal70 where

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

module VC70
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal70 : Set
  goal70 =
    (pointer-memory : Addr → Addr) →
    (post-memory havoc-memory : Addr → Addr) →
    (head current array : Addr) →
    (i2 i i1 i3 i4 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      first-node = pointer-memory head
      current-slot = shift current zeroZ
      current-node = pointer-memory current-slot
      selected-node = pointer-memory (shift array i2)
      upper = addInt i i1
      selected-index =
        lIndexOf pointer-memory selected-node array i1 upper
      array-start = shift array zeroZ
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
    selected-index ≤Z i4 →
    i ≤Z maximumArrayIndexMinusOne →
    addInt twoZ i4 ≤Z upper →
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
      post-memory pointer-memory
      array (addInt oneZ i3)
      (subtractInt upper oneZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z subtractInt upper oneZ →
      Separated
        (post-memory (shift array index)) fourZ
        array-start maximumArrayIndex) →
    ((left-index right-index : Int) →
      left-index ≠ right-index →
      i1 ≤Z right-index →
      i1 ≤Z left-index →
      right-index <Z subtractInt upper oneZ →
      left-index <Z subtractInt upper oneZ →
      Separated
        (post-memory (shift array left-index)) fourZ
        (post-memory (shift array right-index)) fourZ) →
    EqS1List
      (loadS1List
        (updated-pointer-memory (shift array i4))
        float-memory
        updated-pointer-memory)
      (loadS1List
        (pointer-memory (shift array (addInt oneZ i4)))
        float-memory
        pointer-memory)

list-remove-contains-item-post-unchanged-swipe-part5-goal70 : Set₂
list-remove-contains-item-post-unchanged-swipe-part5-goal70 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC70.goal70 {R} region linked index-of-theory
