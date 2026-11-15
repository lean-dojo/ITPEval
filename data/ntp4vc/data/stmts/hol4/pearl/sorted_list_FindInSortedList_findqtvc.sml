(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sorted_list_FindInSortedList_findqtvc: the verification condition for
  searching a sorted integer list, including preservation of sortedness for
  the recursive tail and equivalence of the Boolean result with membership.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory listTheory sortingTheory;

val sorted_list_FindInSortedList_find_vc =
  ``!l : int list.
    !x : int.
      SORTED (\a b : int. a <= b) l ==>
      (case l of
         [] => T
       | y::r =>
           ~(x = y) ==>
           y < x ==>
           (case l of
              [] => F
            | h::f => f = r) /\
           SORTED (\a b : int. a <= b) r) /\
      (!result : bool.
         (case l of
            [] => result = F
          | y::r =>
              if x = y then
                result = T
              else if y < x then
                result = (if MEM x r then T else F)
              else
                result = F) ==>
         ((result = T) <=> MEM x l))``;
