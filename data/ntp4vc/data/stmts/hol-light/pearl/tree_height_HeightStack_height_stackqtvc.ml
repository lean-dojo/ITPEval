(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_height_HeightStack_height_stackqtvc: the verification condition
  for recursive tree-height computation with an explicit stack, including
  its lexicographic decrease obligations and universal result equation.
  This file contains no proof.
*)

let ntp4vc_tree_height_tree_INDUCT,
    ntp4vc_tree_height_tree_RECURSION =
  define_type
    "ntp4vc_tree_height_tree =
       NTP4VCTreeHeightEmpty
     | NTP4VCTreeHeightNode
         ntp4vc_tree_height_tree A ntp4vc_tree_height_tree";;

let ntp4vc_tree_height_int_max = new_definition
 `ntp4vc_tree_height_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_tree_height_size =
  new_recursive_definition ntp4vc_tree_height_tree_RECURSION
   `(ntp4vc_tree_height_size
       (NTP4VCTreeHeightEmpty:A ntp4vc_tree_height_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_tree_height_tree.
     !x:A.
       ntp4vc_tree_height_size
         (NTP4VCTreeHeightNode l x r) =
       (&1:int) +
       ntp4vc_tree_height_size l +
       ntp4vc_tree_height_size r)`;;

let ntp4vc_tree_height_height =
  new_recursive_definition ntp4vc_tree_height_tree_RECURSION
   `(ntp4vc_tree_height_height
       (NTP4VCTreeHeightEmpty:A ntp4vc_tree_height_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_tree_height_tree.
     !x:A.
       ntp4vc_tree_height_height
         (NTP4VCTreeHeightNode l x r) =
       (&1:int) +
       ntp4vc_tree_height_int_max
         (ntp4vc_tree_height_height l)
         (ntp4vc_tree_height_height r))`;;

let ntp4vc_tree_height_heights =
  new_recursive_definition list_RECURSION
   `(ntp4vc_tree_height_heights
       ([]:(int#A ntp4vc_tree_height_tree)list) =
       (&0:int)) /\
    (!p:(int#A ntp4vc_tree_height_tree).
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_heights (CONS p rest) =
       ntp4vc_tree_height_int_max
         (FST p + ntp4vc_tree_height_height (SND p))
         (ntp4vc_tree_height_heights rest))`;;

let ntp4vc_tree_height_sizes =
  new_recursive_definition list_RECURSION
   `(ntp4vc_tree_height_sizes
       ([]:(int#A ntp4vc_tree_height_tree)list) =
       (&0:int)) /\
    (!p:(int#A ntp4vc_tree_height_tree).
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_sizes (CONS p rest) =
       ntp4vc_tree_height_size (SND p) +
       ntp4vc_tree_height_sizes rest)`;;

let ntp4vc_tree_height_tail_is =
  new_recursive_definition list_RECURSION
   `(!target:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_tail_is [] target = F) /\
    (!p:(int#A ntp4vc_tree_height_tree).
     !rest target:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_tail_is (CONS p rest) target =
       (rest = target))`;;

let ntp4vc_tree_height_variant_decreases = new_definition
 `ntp4vc_tree_height_variant_decreases
    (stack:(int#A ntp4vc_tree_height_tree)list)
    (next:(int#A ntp4vc_tree_height_tree)list) <=>
    (((&0:int) <= ntp4vc_tree_height_sizes stack /\
      ntp4vc_tree_height_sizes next <
        ntp4vc_tree_height_sizes stack) \/
     (ntp4vc_tree_height_sizes stack =
        ntp4vc_tree_height_sizes next /\
      ntp4vc_tree_height_tail_is stack next))`;;

let ntp4vc_tree_height_call_branch =
  new_recursive_definition ntp4vc_tree_height_tree_RECURSION
   `(!m h:int.
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_call_branch m h
         (NTP4VCTreeHeightEmpty:A ntp4vc_tree_height_tree) rest =
       (ntp4vc_tree_height_variant_decreases
          (CONS (h,NTP4VCTreeHeightEmpty) rest) rest /\
        (&0:int) <= ntp4vc_tree_height_int_max m h)) /\
    (!m h:int.
     !l r:A ntp4vc_tree_height_tree.
     !x:A.
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_call_branch m h
         (NTP4VCTreeHeightNode l x r) rest =
       (let next =
          CONS (h + (&1:int),l)
            (CONS (h + (&1:int),r) rest) in
        ntp4vc_tree_height_variant_decreases
          (CONS (h,NTP4VCTreeHeightNode l x r) rest) next /\
        (&0:int) <= m))`;;

let ntp4vc_tree_height_call_obligations =
  new_recursive_definition list_RECURSION
   `(!m:int.
       ntp4vc_tree_height_call_obligations m
         ([]:(int#A ntp4vc_tree_height_tree)list) = T) /\
    (!m:int.
     !p:(int#A ntp4vc_tree_height_tree).
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_call_obligations m (CONS p rest) =
       ntp4vc_tree_height_call_branch
         m (FST p) (SND p) rest)`;;

let ntp4vc_tree_height_result_branch =
  new_recursive_definition ntp4vc_tree_height_tree_RECURSION
   `(!m h result:int.
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_result_branch m h
         (NTP4VCTreeHeightEmpty:A ntp4vc_tree_height_tree)
         rest result =
       (result =
        ntp4vc_tree_height_int_max
          (ntp4vc_tree_height_int_max m h)
          (ntp4vc_tree_height_heights rest))) /\
    (!m h result:int.
     !l r:A ntp4vc_tree_height_tree.
     !x:A.
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_result_branch m h
         (NTP4VCTreeHeightNode l x r) rest result =
       (let next =
          CONS (h + (&1:int),l)
            (CONS (h + (&1:int),r) rest) in
        result =
          ntp4vc_tree_height_int_max m
            (ntp4vc_tree_height_heights next)))`;;

let ntp4vc_tree_height_result_premise =
  new_recursive_definition list_RECURSION
   `(!m result:int.
       ntp4vc_tree_height_result_premise m
         ([]:(int#A ntp4vc_tree_height_tree)list) result =
       (result = m)) /\
    (!m result:int.
     !p:(int#A ntp4vc_tree_height_tree).
     !rest:(int#A ntp4vc_tree_height_tree)list.
       ntp4vc_tree_height_result_premise
         m (CONS p rest) result =
       ntp4vc_tree_height_result_branch
         m (FST p) (SND p) rest result)`;;

let statement =
 `!m:int.
  !stack:(int#A ntp4vc_tree_height_tree)list.
    (&0:int) <= m
    ==>
    ntp4vc_tree_height_call_obligations m stack /\
    (!result:int.
       ntp4vc_tree_height_result_premise m stack result
       ==>
       result =
         ntp4vc_tree_height_int_max m
           (ntp4vc_tree_height_heights stack))`;;
