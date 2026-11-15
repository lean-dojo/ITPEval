(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_height_Iteration_height1qtvc: the loop-invariant verification
  condition for iterative binary-tree height computation with explicit
  continuations, including variant decrease, invariant preservation, and the
  final height result. This file contains no proof.
*)

let ntp4vc_thi_tree_INDUCT,ntp4vc_thi_tree_RECURSION =
  define_type
   "ntp4vc_thi_tree =
      NTP4VC_THI_Empty
    | NTP4VC_THI_Node ntp4vc_thi_tree A ntp4vc_thi_tree";;

let ntp4vc_thi_cont_INDUCT,ntp4vc_thi_cont_RECURSION =
  define_type
   "ntp4vc_thi_cont =
      NTP4VC_THI_Id
    | NTP4VC_THI_Kleft (A ntp4vc_thi_tree) ntp4vc_thi_cont
    | NTP4VC_THI_Kright int ntp4vc_thi_cont";;

let ntp4vc_thi_what_INDUCT,ntp4vc_thi_what_RECURSION =
  define_type
   "ntp4vc_thi_what =
      NTP4VC_THI_Argument (A ntp4vc_thi_tree)
    | NTP4VC_THI_Result int";;

let ntp4vc_thi_int_max = new_definition
 `ntp4vc_thi_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_thi_tree_size =
  new_recursive_definition ntp4vc_thi_tree_RECURSION
   `(ntp4vc_thi_tree_size
       (NTP4VC_THI_Empty:A ntp4vc_thi_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_thi_tree.
     !x:A.
       ntp4vc_thi_tree_size (NTP4VC_THI_Node l x r) =
       (&1:int) + ntp4vc_thi_tree_size l + ntp4vc_thi_tree_size r)`;;

let ntp4vc_thi_height =
  new_recursive_definition ntp4vc_thi_tree_RECURSION
   `(ntp4vc_thi_height
       (NTP4VC_THI_Empty:A ntp4vc_thi_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_thi_tree.
     !x:A.
       ntp4vc_thi_height (NTP4VC_THI_Node l x r) =
       (&1:int) +
       ntp4vc_thi_int_max
         (ntp4vc_thi_height l) (ntp4vc_thi_height r))`;;

let ntp4vc_thi_is_id =
  new_recursive_definition ntp4vc_thi_cont_RECURSION
   `(ntp4vc_thi_is_id
       (NTP4VC_THI_Id:A ntp4vc_thi_cont) = T) /\
    (!l:A ntp4vc_thi_tree.
     !k:A ntp4vc_thi_cont.
       ntp4vc_thi_is_id (NTP4VC_THI_Kleft l k) = F) /\
    (!x:int.
     !k:A ntp4vc_thi_cont.
       ntp4vc_thi_is_id (NTP4VC_THI_Kright x k) = F)`;;

let ntp4vc_thi_is_result =
  new_recursive_definition ntp4vc_thi_what_RECURSION
   `(!t:A ntp4vc_thi_tree.
       ntp4vc_thi_is_result (NTP4VC_THI_Argument t) = F) /\
    (!x:int.
       ntp4vc_thi_is_result
         (NTP4VC_THI_Result x:A ntp4vc_thi_what) = T)`;;

let ntp4vc_thi_evalk =
  new_recursive_definition ntp4vc_thi_cont_RECURSION
   `(!r:int.
       ntp4vc_thi_evalk
         (NTP4VC_THI_Id:A ntp4vc_thi_cont) r = r) /\
    (!l:A ntp4vc_thi_tree.
     !k:A ntp4vc_thi_cont.
     !r:int.
       ntp4vc_thi_evalk (NTP4VC_THI_Kleft l k) r =
       ntp4vc_thi_evalk k
         ((&1:int) +
          ntp4vc_thi_int_max (ntp4vc_thi_height l) r)) /\
    (!x:int.
     !k:A ntp4vc_thi_cont.
     !r:int.
       ntp4vc_thi_evalk (NTP4VC_THI_Kright x k) r =
       ntp4vc_thi_evalk k
         ((&1:int) + ntp4vc_thi_int_max x r))`;;

let ntp4vc_thi_evalw =
  new_recursive_definition ntp4vc_thi_what_RECURSION
   `(!t:A ntp4vc_thi_tree.
       ntp4vc_thi_evalw (NTP4VC_THI_Argument t) =
       ntp4vc_thi_height t) /\
    (!x:int.
       ntp4vc_thi_evalw
         (NTP4VC_THI_Result x:A ntp4vc_thi_what) = x)`;;

let ntp4vc_thi_sizek =
  new_recursive_definition ntp4vc_thi_cont_RECURSION
   `(ntp4vc_thi_sizek
       (NTP4VC_THI_Id:A ntp4vc_thi_cont) =
       (&0:int)) /\
    (!t:A ntp4vc_thi_tree.
     !k:A ntp4vc_thi_cont.
       ntp4vc_thi_sizek (NTP4VC_THI_Kleft t k) =
       (&3:int) +
       (&4:int) * ntp4vc_thi_tree_size t +
       ntp4vc_thi_sizek k) /\
    (!x:int.
     !k:A ntp4vc_thi_cont.
       ntp4vc_thi_sizek (NTP4VC_THI_Kright x k) =
       (&1:int) + ntp4vc_thi_sizek k)`;;

let ntp4vc_thi_sizew =
  new_recursive_definition ntp4vc_thi_what_RECURSION
   `(!t:A ntp4vc_thi_tree.
       ntp4vc_thi_sizew (NTP4VC_THI_Argument t) =
       (&1:int) + (&4:int) * ntp4vc_thi_tree_size t) /\
    (!x:int.
       ntp4vc_thi_sizew
         (NTP4VC_THI_Result x:A ntp4vc_thi_what) = (&0:int))`;;

let statement =
 `!t:A ntp4vc_thi_tree.
    ntp4vc_thi_evalk
      (NTP4VC_THI_Id:A ntp4vc_thi_cont)
      (ntp4vc_thi_evalw (NTP4VC_THI_Argument t)) =
    ntp4vc_thi_height t /\
    (!k:A ntp4vc_thi_cont.
     !w:A ntp4vc_thi_what.
       ntp4vc_thi_evalk k (ntp4vc_thi_evalw w) =
       ntp4vc_thi_height t
       ==>
       (!o1:bool.
          (if ntp4vc_thi_is_id k
           then o1 =
             (if ntp4vc_thi_is_result w then T else F)
           else o1 = F)
          ==>
          (if ~(o1 = T)
           then
             ((w =
                 NTP4VC_THI_Argument
                   (NTP4VC_THI_Empty:A ntp4vc_thi_tree) /\
               (((&0:int) <=
                   ntp4vc_thi_sizek k + ntp4vc_thi_sizew w /\
                 ntp4vc_thi_sizek k +
                   ntp4vc_thi_sizew
                     (NTP4VC_THI_Result (&0:int):
                        A ntp4vc_thi_what) <
                 ntp4vc_thi_sizek k + ntp4vc_thi_sizew w) /\
                ntp4vc_thi_evalk k
                  (ntp4vc_thi_evalw
                    (NTP4VC_THI_Result (&0:int):
                       A ntp4vc_thi_what)) =
                ntp4vc_thi_height t)) \/
              (?l r:A ntp4vc_thi_tree.
               ?x:A.
                 w =
                   NTP4VC_THI_Argument
                     (NTP4VC_THI_Node l x r) /\
                 (((&0:int) <=
                     ntp4vc_thi_sizek k + ntp4vc_thi_sizew w /\
                   ntp4vc_thi_sizek (NTP4VC_THI_Kleft r k) +
                     ntp4vc_thi_sizew (NTP4VC_THI_Argument l) <
                   ntp4vc_thi_sizek k + ntp4vc_thi_sizew w) /\
                  ntp4vc_thi_evalk (NTP4VC_THI_Kleft r k)
                    (ntp4vc_thi_evalw
                      (NTP4VC_THI_Argument l)) =
                  ntp4vc_thi_height t)) \/
              (?v:int.
               ?r:A ntp4vc_thi_tree.
               ?k0:A ntp4vc_thi_cont.
                 w = NTP4VC_THI_Result v /\
                 k = NTP4VC_THI_Kleft r k0 /\
                 (((&0:int) <=
                     ntp4vc_thi_sizek k + ntp4vc_thi_sizew w /\
                   ntp4vc_thi_sizek (NTP4VC_THI_Kright v k0) +
                     ntp4vc_thi_sizew (NTP4VC_THI_Argument r) <
                   ntp4vc_thi_sizek k + ntp4vc_thi_sizew w) /\
                  ntp4vc_thi_evalk (NTP4VC_THI_Kright v k0)
                    (ntp4vc_thi_evalw
                      (NTP4VC_THI_Argument r)) =
                  ntp4vc_thi_height t)) \/
              (?v hl:int.
               ?k0:A ntp4vc_thi_cont.
                 w = NTP4VC_THI_Result v /\
                 k = NTP4VC_THI_Kright hl k0 /\
                 (((&0:int) <=
                     ntp4vc_thi_sizek k + ntp4vc_thi_sizew w /\
                   ntp4vc_thi_sizek k0 +
                     ntp4vc_thi_sizew
                       (NTP4VC_THI_Result
                         ((&1:int) +
                          ntp4vc_thi_int_max hl v):
                         A ntp4vc_thi_what) <
                   ntp4vc_thi_sizek k + ntp4vc_thi_sizew w) /\
                  ntp4vc_thi_evalk k0
                    (ntp4vc_thi_evalw
                      (NTP4VC_THI_Result
                        ((&1:int) +
                         ntp4vc_thi_int_max hl v):
                        A ntp4vc_thi_what)) =
                  ntp4vc_thi_height t)))
           else
             ntp4vc_thi_is_result w /\
             (!result:int.
                w = NTP4VC_THI_Result result
                ==> result = ntp4vc_thi_height t))))`;;
