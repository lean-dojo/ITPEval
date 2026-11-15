(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/braun_trees_BraunHeaps_mergeqtvc: a Braun-heap merge verification
  condition preserving heap order, the Braun size invariant, element
  multiplicities, and total size. This file contains no proof.
*)

let braun_merge_tree_INDUCT,braun_merge_tree_RECURSION = define_type
  "braun_merge_tree =
       BraunMergeEmpty
     | BraunMergeNode braun_merge_tree A braun_merge_tree";;

let braun_merge_size =
  new_recursive_definition braun_merge_tree_RECURSION
   `(braun_merge_size (BraunMergeEmpty:A braun_merge_tree) = (&0:int)) /\
    (!l x r.
       braun_merge_size (BraunMergeNode l x r) =
       (&1:int) + braun_merge_size l + braun_merge_size r)`;;

let braun_merge_occ =
  new_recursive_definition braun_merge_tree_RECURSION
   `(!x:A. braun_merge_occ x BraunMergeEmpty = (&0:int)) /\
    (!x y:A.
     !l r:A braun_merge_tree.
       braun_merge_occ x (BraunMergeNode l y r) =
       (if y = x then (&1:int) else (&0:int)) +
       braun_merge_occ x l + braun_merge_occ x r)`;;

let braun_merge_le_root =
  new_recursive_definition braun_merge_tree_RECURSION
   `(!le:A->A->bool.
     !e:A.
       braun_merge_le_root le e BraunMergeEmpty = T) /\
    (!le:A->A->bool.
     !e x:A.
     !l r:A braun_merge_tree.
       braun_merge_le_root le e (BraunMergeNode l x r) = le e x)`;;

let braun_merge_heap =
  new_recursive_definition braun_merge_tree_RECURSION
   `(!le:A->A->bool.
       braun_merge_heap le BraunMergeEmpty = T) /\
    (!le:A->A->bool.
     !x:A.
     !l r:A braun_merge_tree.
       braun_merge_heap le (BraunMergeNode l x r) =
       (braun_merge_le_root le x l /\
        braun_merge_heap le l /\
        braun_merge_le_root le x r /\
        braun_merge_heap le r))`;;

let braun_merge_inv =
  new_recursive_definition braun_merge_tree_RECURSION
   `(braun_merge_inv (BraunMergeEmpty:A braun_merge_tree) = T) /\
    (!x:A.
     !l r:A braun_merge_tree.
       braun_merge_inv (BraunMergeNode l x r) =
       ((braun_merge_size l = braun_merge_size r \/
         braun_merge_size l = braun_merge_size r + (&1:int)) /\
        braun_merge_inv l /\
        braun_merge_inv r))`;;

let braun_merge_ready = new_definition
 `braun_merge_ready
    (le:A->A->bool)
    (l:A braun_merge_tree)
    (r:A braun_merge_tree) <=>
      r = BraunMergeEmpty \/
      (?rl rr:A braun_merge_tree.
       ?rv:A.
       ?ll lr:A braun_merge_tree.
       ?lv:A.
         r = BraunMergeNode rl rv rr /\
         l = BraunMergeNode ll lv lr /\
         (if le lv rv then
            (((&0:int) <= braun_merge_size l + braun_merge_size r /\
              braun_merge_size ll + braun_merge_size lr <
                braun_merge_size l + braun_merge_size r) /\
             (braun_merge_heap le ll /\ braun_merge_heap le lr) /\
             (braun_merge_inv ll /\ braun_merge_inv lr) /\
             braun_merge_size lr <= braun_merge_size ll /\
             braun_merge_size ll <= braun_merge_size lr + (&1:int))
          else
            (braun_merge_heap le l /\
             braun_merge_inv l /\
             (&0:int) < braun_merge_size l) /\
            (!removed:A.
             !l1:A braun_merge_tree.
               braun_merge_heap le l1 /\
               braun_merge_inv l1 /\
               braun_merge_size l1 = braun_merge_size l - (&1:int) /\
               braun_merge_occ removed l1 =
                 braun_merge_occ removed l - (&1:int) /\
               (!other:A.
                  ~(other = removed)
                  ==> braun_merge_occ other l1 =
                      braun_merge_occ other l)
               ==>
               braun_merge_heap le r /\
               braun_merge_inv r /\
               (&0:int) < braun_merge_size r)))`;;

let braun_merge_step = new_definition
 `braun_merge_step
    (le:A->A->bool)
    (minimum:A braun_merge_tree->A)
    (l:A braun_merge_tree)
    (r:A braun_merge_tree)
    (result:A braun_merge_tree) <=>
      (r = BraunMergeEmpty /\ result = l) \/
      (?rl rr:A braun_merge_tree.
       ?rv:A.
       ?ll lr:A braun_merge_tree.
       ?lv:A.
         r = BraunMergeNode rl rv rr /\
         l = BraunMergeNode ll lv lr /\
         (if le lv rv then
            (?o1:A braun_merge_tree.
               (braun_merge_heap le o1 /\
                braun_merge_inv o1 /\
                (!e:A.
                   braun_merge_occ e o1 =
                   braun_merge_occ e ll + braun_merge_occ e lr) /\
                braun_merge_size o1 =
                  braun_merge_size ll + braun_merge_size lr) /\
               result = BraunMergeNode r lv o1)
          else
            (?e:A.
             ?t':A braun_merge_tree.
               (braun_merge_heap le t' /\
                braun_merge_inv t' /\
                braun_merge_size t' =
                  braun_merge_size l - (&1:int) /\
                braun_merge_occ e t' =
                  braun_merge_occ e l - (&1:int) /\
                (!other:A.
                   ~(other = e)
                   ==> braun_merge_occ other t' =
                       braun_merge_occ other l)) /\
               (?o1:A braun_merge_tree.
                  (braun_merge_heap le o1 /\
                   braun_merge_inv o1 /\
                   (if e = minimum r then
                      braun_merge_occ e o1 = braun_merge_occ e r
                    else
                      braun_merge_occ e o1 =
                        braun_merge_occ e r + (&1:int) /\
                      braun_merge_occ (minimum r) o1 =
                        braun_merge_occ (minimum r) r - (&1:int)) /\
                   (!other:A.
                      ~(other = e)
                      ==> ~(other = minimum r)
                      ==> braun_merge_occ other o1 =
                          braun_merge_occ other r) /\
                   braun_merge_size o1 = braun_merge_size r) /\
                  result = BraunMergeNode o1 rv t'))))`;;

let statement =
 `!le:A->A->bool.
  !minimum:A braun_merge_tree->A.
  !l r:A braun_merge_tree.
    ((!x:A. le x x) /\
     (!x y z:A. le x y /\ le y z ==> le x z) /\
     (!x y:A. le x y \/ le y x) /\
     (!tl tr:A braun_merge_tree.
      !x:A.
        minimum (BraunMergeNode tl x tr) = x))
    ==>
    braun_merge_heap le l
    ==>
    braun_merge_heap le r
    ==>
    braun_merge_inv l
    ==>
    braun_merge_inv r
    ==>
    braun_merge_size r <= braun_merge_size l
    ==>
    braun_merge_size l <= braun_merge_size r + (&1:int)
    ==>
    braun_merge_ready le l r /\
    (!result:A braun_merge_tree.
       braun_merge_step le minimum l r result
       ==>
       braun_merge_heap le result /\
       braun_merge_inv result /\
       (!e:A.
          braun_merge_occ e result =
          braun_merge_occ e l + braun_merge_occ e r) /\
       braun_merge_size result =
         braun_merge_size l + braun_merge_size r)`;;
