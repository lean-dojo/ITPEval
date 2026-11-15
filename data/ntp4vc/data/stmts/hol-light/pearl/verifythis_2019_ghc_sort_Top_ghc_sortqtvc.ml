(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_ghc_sortqtvc: the verification condition
  for GHC sorting an integer array, requiring the copied sorted list to
  preserve all occurrences and the final array to be sorted and a permutation
  of the input. This file contains no proof.
*)

let ghc_sort_index = new_definition
 `ghc_sort_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ghc_sort_nth = new_definition
 `ghc_sort_nth (a:int list) (i:int) =
    if ghc_sort_index i < LENGTH a
    then EL (ghc_sort_index i) a
    else (&0:int)`;;

let ghc_sort_map_occ = new_definition
 `ghc_sort_map_occ
    (x:int) (a:int list) (lower:int) (upper:int) =
    (&(CARD
       {i:int |
          lower <= i /\ i < upper /\ ghc_sort_nth a i = x}):int)`;;

let ghc_sort_count = new_definition
 `ghc_sort_count (x:int) (a:int list) =
    (&(CARD
       {i:num |
          i < LENGTH a /\ EL i a = x}):int)`;;

let ghc_sort_sorted = new_definition
 `ghc_sort_sorted (a:int list) <=>
    !i1 i2:int.
      (&0:int) <= i1 /\ i1 <= i2 /\ i2 < (&(LENGTH a):int)
      ==> ghc_sort_nth a i1 <= ghc_sort_nth a i2`;;

let ghc_sort_permut = new_definition
 `ghc_sort_permut (a:int list) (b:int list) <=>
    LENGTH a = LENGTH b /\
    (!x:int. ghc_sort_count x a = ghc_sort_count x b)`;;

let statement =
 `!a:int list.
    if (&(LENGTH a):int) = (&0:int) then
      ghc_sort_sorted a /\ ghc_sort_permut a a
    else
      (&0:int) < (&(LENGTH a):int) /\
      (!l:int list.
         ghc_sort_sorted l /\
         (!x:int.
            ghc_sort_map_occ
              x a (&0:int) (&(LENGTH a):int) =
            ghc_sort_count x l) /\
         LENGTH l = LENGTH a
         ==>
         (((&0:int) <= (&0:int) /\
           (&(LENGTH l):int) =
             (&(LENGTH a):int) - (&0:int)) /\
          (!a1:int list.
             LENGTH a1 = LENGTH a
             ==>
             ((!x:int.
                 (&0:int) <= x /\ x < (&(LENGTH a1):int)
                 ==>
                 ghc_sort_nth a1 x =
                 ghc_sort_nth l (x - (&0:int))) /\
              (!x:int.
                 (&0:int) <= x /\ x < (&0:int)
                 ==>
                 ghc_sort_nth a1 x = ghc_sort_nth a x) /\
              (!x:int.
                 ghc_sort_map_occ
                   x a1 (&0:int) (&(LENGTH a1):int) =
                 ghc_sort_count x l))
             ==>
             ghc_sort_sorted a1 /\ ghc_sort_permut a1 a)))`;;
