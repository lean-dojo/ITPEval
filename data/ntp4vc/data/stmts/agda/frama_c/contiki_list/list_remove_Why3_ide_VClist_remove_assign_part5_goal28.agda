-- Statement-only formalization of the NTP4VC corpus artifact
-- frama_c/contiki_list/list_remove_Why3_ide_VClist_remove_assign_part5_goal28:
-- the list-removal assignment verification condition concludes that the
-- current pointer is the head, is reached from its predecessor, or lies in
-- the remaining array segment, under the stated integer, memory, linked-list,
-- unchanged-region, separation, and pointer-distinctness assumptions.
-- This file contains no proof.

{-# OPTIONS --safe #-}

module ListRemoveAssignPart5Goal28 where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Int using (Int)
open import ListAddFinalAddPreLinked2Part1Goal43

Invalid : (Int → Int) → Addr → Int → Set
Invalid allocation p n =
  zeroZ <Z n →
  Either
    (allocation (Addr.base p) ≤Z Addr.offset p)
    (addInt (Addr.offset p) n ≤Z zeroZ)

Included : Addr → Int → Addr → Int → Set
Included p a q b =
  zeroZ <Z a →
  (zeroZ ≤Z b) ∧
  (Addr.base p ≡ Addr.base q) ∧
  (Addr.offset q ≤Z Addr.offset p) ∧
  (addInt (Addr.offset p) a ≤Z addInt (Addr.offset q) b)

module VC28
  {R : Set}
  (region : Int → Int)
  (linked : (Int → Int) → Set)
  (index-of-theory : IndexOfTheory) where

  open IndexOfTheory index-of-theory

  Framed : (Addr → Addr) → Set
  Framed pointer-memory =
    (p : Addr) →
    region (Addr.base (pointer-memory p)) ≤Z zeroZ

  goal28 : Set
  goal28 =
    (pointer-memory : Addr → Addr) →
    (head current : Addr) →
    (i i1 : Int) →
    (array : Addr) →
    (i2 : Int) →
    (allocation : Int → Int) →
    (float-memory : Addr → R) →
    let
      first-node = pointer-memory head
      current-slot = shift current zeroZ
      current-node = pointer-memory current-slot
      upper = addInt i i1
      array-start = shift array zeroZ
      found-index =
        lIndexOf
          pointer-memory current-node array i1 upper
    in
    first-node ≠ addr zeroZ zeroZ →
    current-node ≠ addr zeroZ zeroZ →
    current-node ≠ first-node →
    zeroZ ≤Z i →
    zeroZ ≤Z i1 →
    i1 ≤Z i2 →
    i2 ≤Z upper →
    region (Addr.base head) ≤Z zeroZ →
    region (Addr.base array) ≤Z zeroZ →
    region (Addr.base current-node) ≤Z zeroZ →
    i ≤Z maximumArrayIndexMinusOne →
    Framed pointer-memory →
    linked allocation →
    IsSint32 i →
    IsSint32 i1 →
    IsSint32 i2 →
    ValidRW allocation head oneZ →
    Not (Invalid allocation current-slot oneZ) →
    ValidRW allocation array-start maximumArrayIndex →
    Separated head oneZ array-start maximumArrayIndex →
    Separated first-node fourZ array-start maximumArrayIndex →
    PLinkedN
      allocation pointer-memory first-node array i1 i
      (addr zeroZ zeroZ) →
    PUnchanged
      allocation pointer-memory float-memory
      allocation pointer-memory float-memory
      array i1 i2 →
    IsSint32 found-index →
    PLinkedN
      allocation pointer-memory current array i2 oneZ
      current-node →
    PLinkedN
      allocation pointer-memory first-node array i1
      (subtractInt i2 i1) current →
    PLinkedN
      allocation pointer-memory current-node array
      (addInt oneZ i2)
      (subtractInt (subtractInt upper oneZ) i2)
      (addr zeroZ zeroZ) →
    ((index : Int) →
      i1 ≤Z index →
      index ≤Z i2 →
      pointer-memory (shift array index) ≠ current-node) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z upper →
      Separated
        head oneZ
        (pointer-memory (shift array index)) fourZ) →
    ((index : Int) →
      i1 ≤Z index →
      index <Z i2 →
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
      node ≠ current-node →
      i1 ≤Z index →
      index <Z upper →
      Separated current-node fourZ node fourZ) →
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
    Either
      (current-slot ≡ head)
      (Either
        (shift
          (pointer-memory
            (shift array (subtractInt found-index oneZ)))
          zeroZ ≡ current-slot)
        (Included
          current-slot oneZ
          (shift array found-index)
          (subtractInt upper found-index)))

list-remove-assign-part5-goal28 : Set₂
list-remove-assign-part5-goal28 =
  (R : Set) →
  (reals : CompleteOrderedField R) →
  RealNumberPresentation reals →
  (region : Int → Int) →
  (linked : (Int → Int) → Set) →
  (index-of-theory : IndexOfTheory) →
  VC28.goal28 {R} region linked index-of-theory
