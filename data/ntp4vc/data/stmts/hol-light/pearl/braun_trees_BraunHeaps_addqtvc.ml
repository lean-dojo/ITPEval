(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_addqtvc: a Braun-heap insertion verification
  condition preserving heap order, the Braun size invariant, element
  multiplicities, and total size. This file contains no proof.
*)

let braun_add_tree_INDUCT,braun_add_tree_RECURSION = define_type
  "braun_add_tree =
       BraunAddEmpty
     | BraunAddNode braun_add_tree A braun_add_tree";;

let braun_add_size =
  new_recursive_definition braun_add_tree_RECURSION
   `(braun_add_size (BraunAddEmpty:A braun_add_tree) = (&0:int)) /\
    (!l x r.
       braun_add_size (BraunAddNode l x r) =
       (&1:int) + braun_add_size l + braun_add_size r)`;;

let braun_add_occ =
  new_recursive_definition braun_add_tree_RECURSION
   `(!x:A. braun_add_occ x BraunAddEmpty = (&0:int)) /\
    (!x y:A.
     !l r:A braun_add_tree.
       braun_add_occ x (BraunAddNode l y r) =
       (if y = x then (&1:int) else (&0:int)) +
       braun_add_occ x l + braun_add_occ x r)`;;

let braun_add_le_root =
  new_recursive_definition braun_add_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       braun_add_le_root le e BraunAddEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !l r:A braun_add_tree.
       braun_add_le_root le e (BraunAddNode l x r) = le e x)`;;

let braun_add_heap =
  new_recursive_definition braun_add_tree_RECURSION
   `(!le:A->A->bool.
       braun_add_heap le BraunAddEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !l r:A braun_add_tree.
       braun_add_heap le (BraunAddNode l x r) =
       (braun_add_le_root le x l /\
        braun_add_heap le l /\
        braun_add_le_root le x r /\
        braun_add_heap le r))`;;

let braun_add_inv =
  new_recursive_definition braun_add_tree_RECURSION
   `(braun_add_inv (BraunAddEmpty:A braun_add_tree) = T) /\
    (!x:A.
     !l r:A braun_add_tree.
       braun_add_inv (BraunAddNode l x r) =
       ((braun_add_size l = braun_add_size r \/
         braun_add_size l = braun_add_size r + (&1:int)) /\
        braun_add_inv l /\
        braun_add_inv r))`;;

let statement =
 `!le:A->A->bool.
  !t:A braun_add_tree.
  !x:A.
    ((!u:A. le u u) /\
     (!u v w:A. le u v /\ le v w ==> le u w) /\
     (!u v:A. le u v \/ le v u))
    ==>
    braun_add_heap le t
    ==>
    braun_add_inv t
    ==>
    ((t = BraunAddEmpty \/
      (?l r:A braun_add_tree.
       ?y:A.
         t = BraunAddNode l y r /\
         (l = r \/ r = r) /\
         braun_add_heap le r /\
         braun_add_inv r)) /\
     (!result:A braun_add_tree.
        ((t = BraunAddEmpty /\
          result = BraunAddNode BraunAddEmpty x BraunAddEmpty) \/
         (?l r:A braun_add_tree.
          ?y:A.
            t = BraunAddNode l y r /\
            (if le x y then
               ?o1:A braun_add_tree.
                 (braun_add_heap le o1 /\
                  braun_add_inv o1 /\
                  braun_add_occ y o1 =
                    braun_add_occ y r + (&1:int) /\
                  (!e:A.
                     ~(e = y)
                     ==> braun_add_occ e o1 = braun_add_occ e r) /\
                  braun_add_size o1 =
                    braun_add_size r + (&1:int)) /\
                 result = BraunAddNode o1 x l
             else
               ?o1:A braun_add_tree.
                 (braun_add_heap le o1 /\
                  braun_add_inv o1 /\
                  braun_add_occ x o1 =
                    braun_add_occ x r + (&1:int) /\
                  (!e:A.
                     ~(e = x)
                     ==> braun_add_occ e o1 = braun_add_occ e r) /\
                  braun_add_size o1 =
                    braun_add_size r + (&1:int)) /\
                 result = BraunAddNode o1 y l)))
        ==>
        braun_add_heap le result /\
        braun_add_inv result /\
        braun_add_occ x result = braun_add_occ x t + (&1:int) /\
        (!e:A.
           ~(e = x)
           ==> braun_add_occ e result = braun_add_occ e t) /\
        braun_add_size result = braun_add_size t + (&1:int)))`;;
