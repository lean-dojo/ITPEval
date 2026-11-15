(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc:
  the verification condition for deleting the minimum node from a nonempty
  pointer-represented binary tree while preserving the tree, root, inorder,
  data, zipper, and left-link update obligations. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  treedel_node = TreedelMemoryNode 'a 'a int
End

val treedel_left_def = Define `
  treedel_left (TreedelMemoryNode left right data) = left`;

val treedel_right_def = Define `
  treedel_right (TreedelMemoryNode left right data) = right`;

val treedel_data_def = Define `
  treedel_data (TreedelMemoryNode left right data) = data`;

Datatype:
  treedel_tree =
    TreedelEmpty
  | TreedelTreeNode treedel_tree 'a treedel_tree
End

val treedel_root_def = Define `
  (treedel_root (null : 'a) TreedelEmpty = null) /\
  (treedel_root null (TreedelTreeNode left p right) = p)`;

val treedel_istree_def = Define `
  (treedel_istree
      (null : 'a)
      (mem : 'a -> 'a treedel_node)
      TreedelEmpty <=>
     T) /\
  (treedel_istree null mem (TreedelTreeNode left p right) <=>
     ~(p = null) /\
     treedel_istree null mem left /\
     treedel_istree null mem right /\
     treedel_root null left = treedel_left (mem p) /\
     treedel_root null right = treedel_right (mem p))`;

val treedel_inorder_def = Define `
  (treedel_inorder (TreedelEmpty : 'a treedel_tree) = []) /\
  (treedel_inorder (TreedelTreeNode left x right) =
     treedel_inorder left ++ x::treedel_inorder right)`;

Datatype:
  treedel_zipper =
    TreedelTop
  | TreedelLeft treedel_zipper 'a ('a treedel_tree)
End

val treedel_zip_def = Define `
  (treedel_zip (t : 'a treedel_tree) TreedelTop = t) /\
  (treedel_zip t (TreedelLeft z x right) =
     treedel_zip (TreedelTreeNode t x right) z)`;

val treedel_inorderz_def = Define `
  (treedel_inorderz (TreedelTop : 'a treedel_zipper) = []) /\
  (treedel_inorderz (TreedelLeft z x right) =
     x::treedel_inorder right ++ treedel_inorderz z)`;

val
  verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc_statement =
  ``!(it : 'loc treedel_tree)
      (mem : 'loc -> 'loc treedel_node)
      (null : 'loc)
      (eq_loc : 'loc -> 'loc -> bool).
      ~(treedel_root null it = null) /\
      treedel_istree null mem it /\
      ALL_DISTINCT (treedel_inorder it)
      ==>
      ~(treedel_root null it = null) /\
      let o1 = treedel_left (mem (treedel_root null it))
      in
      let o2 = null
      in
        (eq_loc o1 o2 <=> o1 = o2) ==>
        if eq_loc o1 o2 then
          ~(treedel_root null it = null) /\
          ~(treedel_root null it = null) /\
          (case it of
             TreedelEmpty => F
           | TreedelTreeNode left p right =>
               treedel_istree null mem right /\
               treedel_root null right =
                 treedel_right (mem (treedel_root null it)) /\
               (case treedel_inorder it of
                  [] => F
                | p1::tail =>
                    treedel_data (mem (treedel_root null it)) =
                      treedel_data (mem p1) /\
                    treedel_inorder right = tail))
        else
          ~(o1 = null) /\
          ~(it = TreedelEmpty) /\
          !o3 : 'loc treedel_tree.
            (case it of
               TreedelEmpty => F
             | TreedelTreeNode left p right => o3 = right)
            ==>
            ~(it = TreedelEmpty) /\
            !o4 : 'loc treedel_tree.
              (case it of
                 TreedelEmpty => F
               | TreedelTreeNode left p right => o4 = left)
              ==>
              ((~(treedel_root null it = null) /\
                treedel_left (mem (treedel_root null it)) = o1) /\
               ~(o1 = null) /\
               (let pt =
                  TreedelTreeNode o4 (treedel_root null it) o3
                in
                  treedel_istree null mem pt /\
                  treedel_zip pt TreedelTop = it)) /\
              !subtree ppr : 'loc treedel_tree.
              !zipper1 : 'loc treedel_zipper.
              !pp : 'loc.
                ~(pp = null) /\
                ~(treedel_left (mem pp) = null) /\
                (let pt = TreedelTreeNode subtree pp ppr
                 in
                   treedel_istree null mem pt /\
                   treedel_zip pt zipper1 = it)
                ==>
                let o5 = null
                in
                  (eq_loc
                     (treedel_left
                        (mem (treedel_left (mem pp))))
                     o5
                   <=>
                   treedel_left
                     (mem (treedel_left (mem pp))) = o5)
                  ==>
                  if
                    ~(eq_loc
                        (treedel_left
                           (mem (treedel_left (mem pp))))
                        o5)
                  then
                    ~(subtree = TreedelEmpty) /\
                    !o6 : 'loc treedel_tree.
                      (case subtree of
                         TreedelEmpty => F
                       | TreedelTreeNode left p right => o6 = right)
                      ==>
                      ~(subtree = TreedelEmpty) /\
                      !o7 : 'loc treedel_tree.
                        (case subtree of
                           TreedelEmpty => F
                         | TreedelTreeNode left p right => o7 = left)
                        ==>
                        ~(treedel_left
                            (mem (treedel_left (mem pp))) = null) /\
                        (case subtree of
                           TreedelEmpty => F
                         | TreedelTreeNode first p second =>
                             first = o7 \/ second = o7) /\
                        ~(treedel_left (mem pp) = null) /\
                        ~(treedel_left
                            (mem (treedel_left (mem pp))) = null) /\
                        (let pt =
                           TreedelTreeNode
                             o7 (treedel_left (mem pp)) o6
                         in
                           treedel_istree null mem pt /\
                           treedel_zip
                             pt
                             (TreedelLeft zipper1 pp ppr) = it)
                  else
                    ~(treedel_left (mem pp) = null) /\
                    ~(treedel_left (mem pp) = null) /\
                    ~(pp = null) /\
                    !mem1 : 'loc -> 'loc treedel_node.
                      mem1 pp =
                        TreedelMemoryNode
                          (treedel_right
                             (mem (treedel_left (mem pp))))
                          (treedel_right (mem pp))
                          (treedel_data (mem pp)) /\
                      (!q : 'loc.
                         ~(q = pp) ==> mem1 q = mem q)
                      ==>
                      ~(subtree = TreedelEmpty) /\
                      !pl : 'loc treedel_tree.
                        (case subtree of
                           TreedelEmpty => F
                         | TreedelTreeNode left p right => pl = left)
                        ==>
                        ~(subtree = TreedelEmpty) /\
                        !o6 : 'loc treedel_tree.
                          (case subtree of
                             TreedelEmpty => F
                           | TreedelTreeNode left p right => o6 = right)
                          ==>
                          (!p : 'loc.
                             treedel_data (mem1 p) =
                               treedel_data (mem p)) /\
                          treedel_istree
                            null
                            mem1
                            (treedel_zip
                               o6
                               (TreedelLeft zipper1 pp ppr)) /\
                          treedel_root
                            null
                            (treedel_zip
                               o6
                               (TreedelLeft zipper1 pp ppr)) =
                            treedel_root null it /\
                          (case treedel_inorder it of
                             [] => F
                           | p::tail =>
                               treedel_data
                                 (mem (treedel_left (mem pp))) =
                                 treedel_data (mem1 p) /\
                               treedel_inorder
                                 (treedel_zip
                                    o6
                                    (TreedelLeft zipper1 pp ppr)) =
                                 tail)``;
