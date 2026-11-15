(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_replace_minqtvc: a Braun-heap minimum
  replacement verification condition preserving heap order, the Braun size
  invariant, element multiplicities, and total size. This file contains no
  proof.
*)

let braun_replace_tree_INDUCT,braun_replace_tree_RECURSION = define_type
  "braun_replace_tree =
       BraunReplaceEmpty
     | BraunReplaceNode braun_replace_tree A braun_replace_tree";;

let braun_replace_size =
  new_recursive_definition braun_replace_tree_RECURSION
   `(braun_replace_size (BraunReplaceEmpty:A braun_replace_tree) =
       (&0:int)) /\
    (!l x r.
       braun_replace_size (BraunReplaceNode l x r) =
       (&1:int) + braun_replace_size l + braun_replace_size r)`;;

let braun_replace_occ =
  new_recursive_definition braun_replace_tree_RECURSION
   `(!x:A.
       braun_replace_occ x BraunReplaceEmpty = (&0:int)) /\
    (!x y:A.
     !l r:A braun_replace_tree.
       braun_replace_occ x (BraunReplaceNode l y r) =
       (if y = x then (&1:int) else (&0:int)) +
       braun_replace_occ x l + braun_replace_occ x r)`;;

let braun_replace_le_root =
  new_recursive_definition braun_replace_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       braun_replace_le_root le e BraunReplaceEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !l r:A braun_replace_tree.
       braun_replace_le_root le e (BraunReplaceNode l x r) = le e x)`;;

let braun_replace_heap =
  new_recursive_definition braun_replace_tree_RECURSION
   `(!le:A->A->bool.
       braun_replace_heap le BraunReplaceEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !l r:A braun_replace_tree.
       braun_replace_heap le (BraunReplaceNode l x r) =
       (braun_replace_le_root le x l /\
        braun_replace_heap le l /\
        braun_replace_le_root le x r /\
        braun_replace_heap le r))`;;

let braun_replace_inv =
  new_recursive_definition braun_replace_tree_RECURSION
   `(braun_replace_inv (BraunReplaceEmpty:A braun_replace_tree) = T) /\
    (!x:A.
     !l r:A braun_replace_tree.
       braun_replace_inv (BraunReplaceNode l x r) =
       ((braun_replace_size l = braun_replace_size r \/
         braun_replace_size l =
           braun_replace_size r + (&1:int)) /\
        braun_replace_inv l /\
        braun_replace_inv r))`;;

let braun_replace_update_spec = new_definition
 `braun_replace_update_spec
    (le:A->A->bool)
    (minimum:A braun_replace_tree->A)
    (x:A)
    (source:A braun_replace_tree)
    (updated:A braun_replace_tree) <=>
      braun_replace_heap le updated /\
      braun_replace_inv updated /\
      (if x = minimum source then
         braun_replace_occ x updated = braun_replace_occ x source
       else
         braun_replace_occ x updated =
           braun_replace_occ x source + (&1:int) /\
         braun_replace_occ (minimum source) updated =
           braun_replace_occ (minimum source) source - (&1:int)) /\
      (!e:A.
         ~(e = x)
         ==> ~(e = minimum source)
         ==> braun_replace_occ e updated = braun_replace_occ e source) /\
      braun_replace_size updated = braun_replace_size source`;;

let braun_replace_ready =
  new_recursive_definition braun_replace_tree_RECURSION
   `(!le:A->A->bool.
     !minimum:A braun_replace_tree->A.
     !x:A.
       braun_replace_ready le minimum x BraunReplaceEmpty = F) /\
    (!le:A->A->bool.
     !minimum:A braun_replace_tree->A.
     !x y:A.
     !l r:A braun_replace_tree.
       braun_replace_ready le minimum x (BraunReplaceNode l y r) =
       (!o1:bool.
          (if braun_replace_le_root le x l then
             o1 =
               (if braun_replace_le_root le x r then T else F)
           else
             o1 = F)
          ==>
          ~(o1 = T)
          ==>
          (braun_replace_heap le l /\
           (&0:int) < braun_replace_size l) /\
          (if braun_replace_le_root le (minimum l) r then
             (l = l \/ r = l) /\
             braun_replace_heap le l /\
             braun_replace_inv l /\
             (&0:int) < braun_replace_size l
           else
             ((l = r \/ r = r) /\
              braun_replace_heap le r /\
              braun_replace_inv r /\
              (&0:int) < braun_replace_size r) /\
             (!o2:A braun_replace_tree.
                braun_replace_update_spec le minimum x r o2
                ==>
                braun_replace_heap le r /\
                (&0:int) < braun_replace_size r))))`;;

let braun_replace_step =
  new_recursive_definition braun_replace_tree_RECURSION
   `(!le:A->A->bool.
     !minimum:A braun_replace_tree->A.
     !x:A.
     !result:A braun_replace_tree.
       braun_replace_step le minimum x result BraunReplaceEmpty = F) /\
    (!le:A->A->bool.
     !minimum:A braun_replace_tree->A.
     !x y:A.
     !l r result:A braun_replace_tree.
       braun_replace_step
         le minimum x result (BraunReplaceNode l y r) =
       (?o1:bool.
          (if braun_replace_le_root le x l then
             o1 =
               (if braun_replace_le_root le x r then T else F)
           else
             o1 = F) /\
          (if o1 = T then
             result = BraunReplaceNode l x r
           else if braun_replace_le_root le (minimum l) r then
             ?o2:A braun_replace_tree.
               braun_replace_update_spec le minimum x l o2 /\
               result = BraunReplaceNode o2 (minimum l) r
           else
             ?o2:A braun_replace_tree.
               braun_replace_update_spec le minimum x r o2 /\
               result = BraunReplaceNode l (minimum r) o2)))`;;

let statement =
 `!le:A->A->bool.
  !minimum:A braun_replace_tree->A.
  !t:A braun_replace_tree.
  !x:A.
    ((!u:A. le u u) /\
     (!u v w:A. le u v /\ le v w ==> le u w) /\
     (!u v:A. le u v \/ le v u) /\
     (!l r:A braun_replace_tree.
      !y:A.
        minimum (BraunReplaceNode l y r) = y))
    ==>
    braun_replace_heap le t
    ==>
    braun_replace_inv t
    ==>
    (&0:int) < braun_replace_size t
    ==>
    braun_replace_ready le minimum x t /\
    (!result:A braun_replace_tree.
       braun_replace_step le minimum x result t
       ==>
       braun_replace_update_spec le minimum x t result)`;;
