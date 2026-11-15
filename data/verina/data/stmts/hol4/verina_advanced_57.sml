(*
  Statement-only formalization of VERINA artifact verina_advanced_57,
  cataloged as "nextGreaterElement": the executable monotonic-stack program
  returns, for each distinct requested integer, the first greater integer to
  its right in the containing distinct list, or -1 when none exists. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory optionTheory pairTheory;

val nextGreaterElement_precond_def = new_definition (
  "nextGreaterElement_precond_def",
  ``nextGreaterElement_precond
      (nums1 : int list) (nums2 : int list) <=>
      ALL_DISTINCT nums1 /\
      ALL_DISTINCT nums2 /\
      EVERY (\x : int. MEM x nums2) nums1``
);

val nextGreaterElement_processStack_def = Define `
  (nextGreaterElement_processStack
      (current : int)
      ([] : int list)
      (nextMap : (int # int) list) =
     (([] : int list), nextMap)) /\
  (nextGreaterElement_processStack
      current
      (top::rest)
      nextMap =
     if current > top then
       nextGreaterElement_processStack
         current rest ((top, current)::nextMap)
     else
       (top::rest, nextMap))
`;

val nextGreaterElement_mapLoop_def = Define `
  (nextGreaterElement_mapLoop
      ([] : int list)
      (stack : int list)
      (nextMap : (int # int) list) =
     FOLDL
       (\acc top. (top, (-1 : int))::acc)
       nextMap
       stack) /\
  (nextGreaterElement_mapLoop
      (current::remaining)
      stack
      nextMap =
     let processed =
       nextGreaterElement_processStack current stack nextMap
     in
       nextGreaterElement_mapLoop
         remaining
         (current::FST processed)
         (SND processed))
`;

val nextGreaterElement_buildMap_def = new_definition (
  "nextGreaterElement_buildMap_def",
  ``nextGreaterElement_buildMap (nums2 : int list) =
      nextGreaterElement_mapLoop
        nums2
        ([] : int list)
        ([] : (int # int) list)``
);

val nextGreaterElement_findInMap_def = Define `
  (nextGreaterElement_findInMap
      ([] : (int # int) list)
      (value : int) =
     (-1 : int)) /\
  (nextGreaterElement_findInMap
      ((key, nextGreater)::rest)
      value =
     if key = value then
       nextGreater
     else
       nextGreaterElement_findInMap rest value)
`;

val nextGreaterElement_resultLoop_def = Define `
  (nextGreaterElement_resultLoop
      ([] : int list)
      (nextMap : (int # int) list)
      (acc : int list) =
     REVERSE acc) /\
  (nextGreaterElement_resultLoop
      (value::remaining)
      nextMap
      acc =
     nextGreaterElement_resultLoop
       remaining
       nextMap
       (nextGreaterElement_findInMap nextMap value::acc))
`;

val nextGreaterElement_def = new_definition (
  "nextGreaterElement_def",
  ``nextGreaterElement
      (nums1 : int list) (nums2 : int list) =
      nextGreaterElement_resultLoop
        nums1
        (nextGreaterElement_buildMap nums2)
        ([] : int list)``
);

val nextGreaterElement_findIndexFrom_def = Define `
  (nextGreaterElement_findIndexFrom
      (value : int)
      (index : num)
      ([] : int list) =
     NONE) /\
  (nextGreaterElement_findIndexFrom
      value
      index
      (x::xs) =
     if x = value then
       SOME index
     else
       nextGreaterElement_findIndexFrom value (index + 1) xs)
`;

val nextGreaterElement_findGreaterOffset_def = Define `
  (nextGreaterElement_findGreaterOffset
      (value : int)
      (offset : num)
      ([] : int list) =
     NONE) /\
  (nextGreaterElement_findGreaterOffset
      value
      offset
      (x::xs) =
     if x > value then
       SOME offset
     else
       nextGreaterElement_findGreaterOffset value (offset + 1) xs)
`;

val nextGreaterElement_resultAt_def = new_definition (
  "nextGreaterElement_resultAt_def",
  ``nextGreaterElement_resultAt
      (nums2 : int list)
      (value : int)
      (resultValue : int) <=>
      case nextGreaterElement_findIndexFrom value 0 nums2 of
        NONE => F
      | SOME index =>
          case
            nextGreaterElement_findGreaterOffset
              value 0 (DROP (index + 1) nums2)
          of
            NONE => resultValue = -1
          | SOME offset =>
              resultValue = EL (index + offset + 1) nums2``
);

val nextGreaterElement_postcond_def = new_definition (
  "nextGreaterElement_postcond_def",
  ``nextGreaterElement_postcond
      (nums1 : int list)
      (nums2 : int list)
      (result : int list) <=>
      LENGTH result = LENGTH nums1 /\
      EVERY
        (\index : num.
           nextGreaterElement_resultAt
             nums2 (EL index nums1) (EL index result))
        (COUNT_LIST (LENGTH nums1)) /\
      EVERY
        (\value : int. value = -1 \/ MEM value nums2)
        result``
);

val nextGreaterElement_spec_satisfied =
  ``!(nums1 : int list) (nums2 : int list).
      nextGreaterElement_precond nums1 nums2 ==>
      nextGreaterElement_postcond
        nums1 nums2 (nextGreaterElement nums1 nums2)``;
