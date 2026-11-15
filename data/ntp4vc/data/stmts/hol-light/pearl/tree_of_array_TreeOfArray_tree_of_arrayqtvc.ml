(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/tree_of_array_TreeOfArray_tree_of_arrayqtvc: the verification
  condition for constructing a binary tree from an arbitrary array while
  preserving inorder traversal and logarithmic height bounds. This file
  contains no proof.
*)

let ntp4vc_tree_of_array_tree_INDUCT,
    ntp4vc_tree_of_array_tree_RECURSION =
  define_type
    "ntp4vc_tree_of_array_tree =
       NTP4VCTreeOfArrayEmpty
     | NTP4VCTreeOfArrayNode
         ntp4vc_tree_of_array_tree A ntp4vc_tree_of_array_tree";;

let ntp4vc_tree_of_array_size =
  new_recursive_definition ntp4vc_tree_of_array_tree_RECURSION
   `(ntp4vc_tree_of_array_size
       (NTP4VCTreeOfArrayEmpty:A ntp4vc_tree_of_array_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_tree_of_array_tree.
     !x:A.
       ntp4vc_tree_of_array_size
         (NTP4VCTreeOfArrayNode l x r) =
       (&1:int) +
       ntp4vc_tree_of_array_size l +
       ntp4vc_tree_of_array_size r)`;;

let ntp4vc_tree_of_array_int_max = new_definition
 `ntp4vc_tree_of_array_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_tree_of_array_height =
  new_recursive_definition ntp4vc_tree_of_array_tree_RECURSION
   `(ntp4vc_tree_of_array_height
       (NTP4VCTreeOfArrayEmpty:A ntp4vc_tree_of_array_tree) =
       (&0:int)) /\
    (!l r:A ntp4vc_tree_of_array_tree.
     !x:A.
       ntp4vc_tree_of_array_height
         (NTP4VCTreeOfArrayNode l x r) =
       (&1:int) +
       ntp4vc_tree_of_array_int_max
         (ntp4vc_tree_of_array_height l)
         (ntp4vc_tree_of_array_height r))`;;

let ntp4vc_tree_of_array_inorder =
  new_recursive_definition ntp4vc_tree_of_array_tree_RECURSION
   `(ntp4vc_tree_of_array_inorder
       (NTP4VCTreeOfArrayEmpty:A ntp4vc_tree_of_array_tree) =
       ([]:A list)) /\
    (!l r:A ntp4vc_tree_of_array_tree.
     !x:A.
       ntp4vc_tree_of_array_inorder
         (NTP4VCTreeOfArrayNode l x r) =
       APPEND
         (ntp4vc_tree_of_array_inorder l)
         (CONS x (ntp4vc_tree_of_array_inorder r)))`;;

let ntp4vc_tree_of_array_take =
  new_recursive_definition list_RECURSION
   `(!n:num.
       ntp4vc_tree_of_array_take n ([]:A list) = []) /\
    (!n:num. !h:A. !t:A list.
       ntp4vc_tree_of_array_take n (CONS h t) =
       if n = 0 then []
       else CONS h (ntp4vc_tree_of_array_take (PRE n) t))`;;

let ntp4vc_tree_of_array_drop =
  new_recursive_definition list_RECURSION
   `(!n:num.
       ntp4vc_tree_of_array_drop n ([]:A list) = []) /\
    (!n:num. !h:A. !t:A list.
       ntp4vc_tree_of_array_drop n (CONS h t) =
       if n = 0 then CONS h t
       else ntp4vc_tree_of_array_drop (PRE n) t)`;;

let ntp4vc_tree_of_array_int_power = new_definition
 `ntp4vc_tree_of_array_int_power (base:int) (exponent:int) =
    base pow
      (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let statement =
 `!a:A list.
    let o1 = (&(LENGTH a):int) in
    (((&0:int) <= (&0:int) /\
      (&0:int) <= o1 /\
      o1 <= (&(LENGTH a):int)) /\
     (!result:A ntp4vc_tree_of_array_tree.
        (let n = o1 - (&0:int) in
         ntp4vc_tree_of_array_size result = n /\
         ntp4vc_tree_of_array_inorder result =
           ntp4vc_tree_of_array_drop 0
             (ntp4vc_tree_of_array_take (num_of_int o1 - 0) a) /\
         ((&0:int) < n
          ==>
          (let h = ntp4vc_tree_of_array_height result in
           ntp4vc_tree_of_array_int_power
             (&2:int) (h - (&1:int)) <= n /\
           n <
             ntp4vc_tree_of_array_int_power (&2:int) h)))
        ==>
        ntp4vc_tree_of_array_inorder result =
          ntp4vc_tree_of_array_drop 0
            (ntp4vc_tree_of_array_take (LENGTH a - 0) a) /\
        ((&0:int) < ntp4vc_tree_of_array_size result
         ==>
         (let h = ntp4vc_tree_of_array_height result in
          ntp4vc_tree_of_array_int_power
            (&2:int) (h - (&1:int)) <=
          ntp4vc_tree_of_array_size result /\
          ntp4vc_tree_of_array_size result <
            ntp4vc_tree_of_array_int_power (&2:int) h))))`;;
