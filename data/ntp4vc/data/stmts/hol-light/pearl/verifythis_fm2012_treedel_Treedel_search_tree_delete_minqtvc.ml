(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_fm2012_treedel_Treedel_search_tree_delete_minqtvc:
  the verification condition for deleting the minimum node from a nonempty
  pointer-represented binary tree, preserving its memory/tree relation and
  describing the resulting inorder traversal. This file contains no proof.
*)

let ntp4vc_treedel_tree_INDUCT,ntp4vc_treedel_tree_RECURSION =
  define_type
   "ntp4vc_treedel_tree =
      NTP4VCTreedelEmpty
    | NTP4VCTreedelNode
        ntp4vc_treedel_tree A ntp4vc_treedel_tree";;

let ntp4vc_treedel_memnode_INDUCT,ntp4vc_treedel_memnode_RECURSION =
  define_type
   "ntp4vc_treedel_memnode =
      NTP4VCTreedelMemNode A A int";;

let ntp4vc_treedel_zipper_INDUCT,ntp4vc_treedel_zipper_RECURSION =
  define_type
   "ntp4vc_treedel_zipper =
      NTP4VCTreedelTop
    | NTP4VCTreedelLeft
        ntp4vc_treedel_zipper A (A ntp4vc_treedel_tree)";;

let ntp4vc_treedel_left =
  new_recursive_definition ntp4vc_treedel_memnode_RECURSION
   `!l r:A.
    !d:int.
      ntp4vc_treedel_left (NTP4VCTreedelMemNode l r d) = l`;;

let ntp4vc_treedel_right =
  new_recursive_definition ntp4vc_treedel_memnode_RECURSION
   `!l r:A.
    !d:int.
      ntp4vc_treedel_right (NTP4VCTreedelMemNode l r d) = r`;;

let ntp4vc_treedel_data =
  new_recursive_definition ntp4vc_treedel_memnode_RECURSION
   `!l r:A.
    !d:int.
      ntp4vc_treedel_data (NTP4VCTreedelMemNode l r d) = d`;;

let ntp4vc_treedel_root =
  new_recursive_definition ntp4vc_treedel_tree_RECURSION
   `(!null:A.
       ntp4vc_treedel_root null
         (NTP4VCTreedelEmpty:A ntp4vc_treedel_tree) = null) /\
    (!null p:A.
     !l r:A ntp4vc_treedel_tree.
       ntp4vc_treedel_root null (NTP4VCTreedelNode l p r) = p)`;;

let ntp4vc_treedel_inorder =
  new_recursive_definition ntp4vc_treedel_tree_RECURSION
   `(ntp4vc_treedel_inorder
       (NTP4VCTreedelEmpty:A ntp4vc_treedel_tree) = []) /\
    (!p:A.
     !l r:A ntp4vc_treedel_tree.
       ntp4vc_treedel_inorder (NTP4VCTreedelNode l p r) =
       APPEND (ntp4vc_treedel_inorder l)
         (CONS p (ntp4vc_treedel_inorder r)))`;;

let ntp4vc_treedel_distinct =
  new_recursive_definition list_RECURSION
   `(ntp4vc_treedel_distinct ([]:A list) = T) /\
    (!x:A.
     !xs:A list.
       ntp4vc_treedel_distinct (CONS x xs) =
       (~(MEM x xs) /\ ntp4vc_treedel_distinct xs))`;;

let ntp4vc_treedel_istree =
  new_recursive_definition ntp4vc_treedel_tree_RECURSION
   `(!null:A.
     !mem:A->A ntp4vc_treedel_memnode.
       ntp4vc_treedel_istree null mem
         (NTP4VCTreedelEmpty:A ntp4vc_treedel_tree) = T) /\
    (!null p:A.
     !mem:A->A ntp4vc_treedel_memnode.
     !l r:A ntp4vc_treedel_tree.
       ntp4vc_treedel_istree null mem (NTP4VCTreedelNode l p r) =
       (~(p = null) /\
        ntp4vc_treedel_istree null mem l /\
        ntp4vc_treedel_istree null mem r /\
        ntp4vc_treedel_root null l =
          ntp4vc_treedel_left (mem p) /\
        ntp4vc_treedel_root null r =
          ntp4vc_treedel_right (mem p)))`;;

let ntp4vc_treedel_zip =
  new_recursive_definition ntp4vc_treedel_zipper_RECURSION
   `(!t:A ntp4vc_treedel_tree.
       ntp4vc_treedel_zip t
         (NTP4VCTreedelTop:A ntp4vc_treedel_zipper) = t) /\
    (!t r:A ntp4vc_treedel_tree.
     !x:A.
     !z:A ntp4vc_treedel_zipper.
       ntp4vc_treedel_zip t (NTP4VCTreedelLeft z x r) =
       ntp4vc_treedel_zip (NTP4VCTreedelNode t x r) z)`;;

let statement =
 `!null:A.
  !eq_loc:A->A->bool.
  !it:A ntp4vc_treedel_tree.
  !mem:A->A ntp4vc_treedel_memnode.
    ~(ntp4vc_treedel_root null it = null)
    ==>
    ntp4vc_treedel_istree null mem it
    ==>
    ntp4vc_treedel_distinct (ntp4vc_treedel_inorder it)
    ==>
    ~(ntp4vc_treedel_root null it = null) /\
    (let o1 =
       ntp4vc_treedel_left
         (mem (ntp4vc_treedel_root null it)) in
     let o2 = null in
       (eq_loc o1 o2 <=> o1 = o2)
       ==>
       (if eq_loc o1 o2 then
          ~(ntp4vc_treedel_root null it = null) /\
          ~(ntp4vc_treedel_root null it = null) /\
          (?l r:A ntp4vc_treedel_tree.
           ?p:A.
             it = NTP4VCTreedelNode l p r /\
             ntp4vc_treedel_istree null mem r /\
             ntp4vc_treedel_root null r =
               ntp4vc_treedel_right
                 (mem (ntp4vc_treedel_root null it)) /\
             (?p0:A.
              ?l1:A list.
                ntp4vc_treedel_inorder it = CONS p0 l1 /\
                ntp4vc_treedel_data
                  (mem (ntp4vc_treedel_root null it)) =
                ntp4vc_treedel_data (mem p0) /\
                ntp4vc_treedel_inorder r = l1))
        else
          ~(o1 = null) /\
          ~(it = (NTP4VCTreedelEmpty:A ntp4vc_treedel_tree)) /\
          (!o3:A ntp4vc_treedel_tree.
             (?l:A ntp4vc_treedel_tree.
              ?p:A.
                it = NTP4VCTreedelNode l p o3)
             ==>
             ~(it =
               (NTP4VCTreedelEmpty:A ntp4vc_treedel_tree)) /\
             (!o4:A ntp4vc_treedel_tree.
                (?p:A.
                 ?r:A ntp4vc_treedel_tree.
                   it = NTP4VCTreedelNode o4 p r)
                ==>
                ((~(ntp4vc_treedel_root null it = null) /\
                  ntp4vc_treedel_left
                    (mem (ntp4vc_treedel_root null it)) = o1) /\
                 ~(o1 = null) /\
                 (let pt =
                    NTP4VCTreedelNode o4
                      (ntp4vc_treedel_root null it) o3 in
                    ntp4vc_treedel_istree null mem pt /\
                    ntp4vc_treedel_zip pt
                      (NTP4VCTreedelTop:
                         A ntp4vc_treedel_zipper) = it)) /\
                (!subtree ppr:A ntp4vc_treedel_tree.
                 !zipper1:A ntp4vc_treedel_zipper.
                 !pp:A.
                   ~(pp = null) /\
                   ~(ntp4vc_treedel_left (mem pp) = null) /\
                   (let pt =
                      NTP4VCTreedelNode subtree pp ppr in
                      ntp4vc_treedel_istree null mem pt /\
                      ntp4vc_treedel_zip pt zipper1 = it)
                   ==>
                   (let o5 = null in
                      (eq_loc
                         (ntp4vc_treedel_left
                           (mem
                             (ntp4vc_treedel_left (mem pp))))
                         o5
                       <=>
                       ntp4vc_treedel_left
                         (mem
                           (ntp4vc_treedel_left (mem pp))) = o5)
                      ==>
                      (if
                         ~(eq_loc
                           (ntp4vc_treedel_left
                             (mem
                               (ntp4vc_treedel_left (mem pp))))
                           o5)
                       then
                         ~(subtree =
                           (NTP4VCTreedelEmpty:
                              A ntp4vc_treedel_tree)) /\
                         (!o6:A ntp4vc_treedel_tree.
                            (?l:A ntp4vc_treedel_tree.
                             ?p:A.
                               subtree =
                                 NTP4VCTreedelNode l p o6)
                            ==>
                            ~(subtree =
                              (NTP4VCTreedelEmpty:
                                 A ntp4vc_treedel_tree)) /\
                            (!o7:A ntp4vc_treedel_tree.
                               (?p:A.
                                ?r:A ntp4vc_treedel_tree.
                                  subtree =
                                    NTP4VCTreedelNode o7 p r)
                               ==>
                               ~(ntp4vc_treedel_left
                                   (mem
                                     (ntp4vc_treedel_left
                                       (mem pp))) = null) /\
                               (?f f1:A ntp4vc_treedel_tree.
                                ?x:A.
                                  subtree =
                                    NTP4VCTreedelNode f x f1 /\
                                  (f = o7 \/ f1 = o7)) /\
                               ~(ntp4vc_treedel_left
                                   (mem pp) = null) /\
                               ~(ntp4vc_treedel_left
                                   (mem
                                     (ntp4vc_treedel_left
                                       (mem pp))) = null) /\
                               (let pt =
                                  NTP4VCTreedelNode o7
                                    (ntp4vc_treedel_left (mem pp))
                                    o6 in
                                  ntp4vc_treedel_istree
                                    null mem pt /\
                                  ntp4vc_treedel_zip pt
                                    (NTP4VCTreedelLeft
                                      zipper1 pp ppr) = it)))
                       else
                         ~(ntp4vc_treedel_left
                             (mem pp) = null) /\
                         ~(ntp4vc_treedel_left
                             (mem pp) = null) /\
                         ~(pp = null) /\
                         (!mem1:A->A ntp4vc_treedel_memnode.
                            mem1 pp =
                              (let x_q = mem pp in
                               NTP4VCTreedelMemNode
                                 (ntp4vc_treedel_right
                                   (mem
                                     (ntp4vc_treedel_left
                                       (mem pp))))
                                 (ntp4vc_treedel_right x_q)
                                 (ntp4vc_treedel_data x_q)) /\
                            (!q:A.
                               ~(q = pp) ==> mem1 q = mem q)
                            ==>
                            ~(subtree =
                              (NTP4VCTreedelEmpty:
                                 A ntp4vc_treedel_tree)) /\
                            (!pl:A ntp4vc_treedel_tree.
                               (?p:A.
                                ?r:A ntp4vc_treedel_tree.
                                  subtree =
                                    NTP4VCTreedelNode pl p r)
                               ==>
                               ~(subtree =
                                 (NTP4VCTreedelEmpty:
                                    A ntp4vc_treedel_tree)) /\
                               (!o6:A ntp4vc_treedel_tree.
                                  (?l:A ntp4vc_treedel_tree.
                                   ?p:A.
                                     subtree =
                                       NTP4VCTreedelNode l p o6)
                                  ==>
                                  (!p:A.
                                     ntp4vc_treedel_data
                                       (mem1 p) =
                                     ntp4vc_treedel_data
                                       (mem p)) /\
                                  ntp4vc_treedel_istree null mem1
                                    (ntp4vc_treedel_zip o6
                                      (NTP4VCTreedelLeft
                                        zipper1 pp ppr)) /\
                                  ntp4vc_treedel_root null
                                    (ntp4vc_treedel_zip o6
                                      (NTP4VCTreedelLeft
                                        zipper1 pp ppr)) =
                                  ntp4vc_treedel_root null it /\
                                  (?p:A.
                                   ?l:A list.
                                     ntp4vc_treedel_inorder it =
                                       CONS p l /\
                                     ntp4vc_treedel_data
                                       (mem
                                         (ntp4vc_treedel_left
                                           (mem pp))) =
                                     ntp4vc_treedel_data
                                       (mem1 p) /\
                                     ntp4vc_treedel_inorder
                                       (ntp4vc_treedel_zip o6
                                         (NTP4VCTreedelLeft
                                           zipper1 pp ppr)) =
                                     l)))))))))))`;;
