(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2021_dll_to_bst_Top_dll_to_bstqtvc: conversion of a
  doubly linked list into a balanced binary-search tree, preserving finite-map
  domains, inorder locations, tree size, and logarithmic height bounds. This
  file contains no proof.
*)

let ntp4vc_dll_bst_tree_INDUCT,
    ntp4vc_dll_bst_tree_RECURSION =
  define_type
    "ntp4vc_dll_bst_tree =
       NTP4VCDllBstEmpty
     | NTP4VCDllBstNode
         ntp4vc_dll_bst_tree int ntp4vc_dll_bst_tree";;

let ntp4vc_dll_bst_int_index = new_definition
 `ntp4vc_dll_bst_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_dll_bst_nth = new_definition
 `ntp4vc_dll_bst_nth (xs:A list) (i:int) =
    if ntp4vc_dll_bst_int_index i < LENGTH xs
    then EL (ntp4vc_dll_bst_int_index i) xs
    else ARB`;;

let ntp4vc_dll_bst_fmap_domain = new_definition
 `ntp4vc_dll_bst_fmap_domain (m:A->B option) =
    {key:A | ?value:B. m key = SOME value}`;;

let ntp4vc_dll_bst_fmap_lookup = new_definition
 `ntp4vc_dll_bst_fmap_lookup (key:A) (m:A->B option) =
    @value:B. m key = SOME value`;;

let ntp4vc_dll_bst_valid = new_definition
 `ntp4vc_dll_bst_valid
    (null:A)
    (prev:A->A option)
    (next:A->A option)
    (s:A list) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH s):int)
      ==>
      ~(ntp4vc_dll_bst_nth s i = null) /\
      ntp4vc_dll_bst_nth s i IN
        ntp4vc_dll_bst_fmap_domain prev /\
      ntp4vc_dll_bst_nth s i IN
        ntp4vc_dll_bst_fmap_domain next /\
      (!j:int.
         i < j /\ j < (&(LENGTH s):int)
         ==> ~(ntp4vc_dll_bst_nth s i =
               ntp4vc_dll_bst_nth s j))`;;

let ntp4vc_dll_bst_dll = new_definition
 `ntp4vc_dll_bst_dll
    (null:A)
    (prev:A->A option)
    (next:A->A option)
    (s:A list)
    (head:A)
    (lo:int)
    (hi:int) <=>
    ntp4vc_dll_bst_valid null prev next s /\
    (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
    head =
      (if lo = (&(LENGTH s):int)
       then null
       else ntp4vc_dll_bst_nth s lo) /\
    (!i:int.
       lo <= i /\ i < hi - (&1:int)
       ==>
       ntp4vc_dll_bst_fmap_lookup
         (ntp4vc_dll_bst_nth s i) next =
       ntp4vc_dll_bst_nth s (i + (&1:int))) /\
    (!i:int.
       lo < i /\ i < hi
       ==>
       ntp4vc_dll_bst_fmap_lookup
         (ntp4vc_dll_bst_nth s i) prev =
       ntp4vc_dll_bst_nth s (i - (&1:int))) /\
    (lo < hi
     ==>
     ntp4vc_dll_bst_fmap_lookup
       (ntp4vc_dll_bst_nth s (hi - (&1:int))) next =
     (if hi = (&(LENGTH s):int)
      then null
      else ntp4vc_dll_bst_nth s hi)) /\
    (lo < hi
     ==>
     ntp4vc_dll_bst_fmap_lookup
       (ntp4vc_dll_bst_nth s lo) prev =
     (if lo = (&0:int)
      then null
      else ntp4vc_dll_bst_nth s (lo - (&1:int))))`;;

let ntp4vc_dll_bst_tree =
  new_recursive_definition ntp4vc_dll_bst_tree_RECURSION
   `(!null:A.
     !prev next:A->A option.
     !s:A list.
     !root:A.
     !lo hi:int.
       ntp4vc_dll_bst_tree
         null prev next s root NTP4VCDllBstEmpty lo hi <=>
       ntp4vc_dll_bst_valid null prev next s /\
       (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
       root = null /\ lo = hi) /\
    (!null:A.
     !prev next:A->A option.
     !s:A list.
     !root:A.
     !left right:ntp4vc_dll_bst_tree.
     !position lo hi:int.
       ntp4vc_dll_bst_tree
         null prev next s root
         (NTP4VCDllBstNode left position right) lo hi <=>
       ntp4vc_dll_bst_valid null prev next s /\
       (&0:int) <= lo /\ lo <= hi /\ hi <= (&(LENGTH s):int) /\
       lo <= position /\ position < hi /\
       root = ntp4vc_dll_bst_nth s position /\
       ntp4vc_dll_bst_tree
         null prev next s
         (ntp4vc_dll_bst_fmap_lookup root prev)
         left lo position /\
       ntp4vc_dll_bst_tree
         null prev next s
         (ntp4vc_dll_bst_fmap_lookup root next)
         right (position + (&1:int)) hi)`;;

let ntp4vc_dll_bst_size =
  new_recursive_definition ntp4vc_dll_bst_tree_RECURSION
   `(ntp4vc_dll_bst_size NTP4VCDllBstEmpty = (&0:int)) /\
    (!left right:ntp4vc_dll_bst_tree.
     !position:int.
       ntp4vc_dll_bst_size
         (NTP4VCDllBstNode left position right) =
       (&1:int) +
       ntp4vc_dll_bst_size left +
       ntp4vc_dll_bst_size right)`;;

let ntp4vc_dll_bst_int_max = new_definition
 `ntp4vc_dll_bst_int_max (x:int) (y:int) =
    if x <= y then y else x`;;

let ntp4vc_dll_bst_height =
  new_recursive_definition ntp4vc_dll_bst_tree_RECURSION
   `(ntp4vc_dll_bst_height NTP4VCDllBstEmpty = (&0:int)) /\
    (!left right:ntp4vc_dll_bst_tree.
     !position:int.
       ntp4vc_dll_bst_height
         (NTP4VCDllBstNode left position right) =
       (&1:int) +
       ntp4vc_dll_bst_int_max
         (ntp4vc_dll_bst_height left)
         (ntp4vc_dll_bst_height right))`;;

let ntp4vc_dll_bst_inorder =
  new_recursive_definition ntp4vc_dll_bst_tree_RECURSION
   `(!s:A list.
       ntp4vc_dll_bst_inorder s NTP4VCDllBstEmpty = []) /\
    (!s:A list.
     !left right:ntp4vc_dll_bst_tree.
     !position:int.
       ntp4vc_dll_bst_inorder
         s (NTP4VCDllBstNode left position right) =
       APPEND
         (ntp4vc_dll_bst_inorder s left)
         (CONS
            (ntp4vc_dll_bst_nth s position)
            (ntp4vc_dll_bst_inorder s right)))`;;

let ntp4vc_dll_bst_int_power = new_definition
 `ntp4vc_dll_bst_int_power (base:int) (exponent:int) =
    base pow
      (if exponent < (&0:int) then 0 else num_of_int exponent)`;;

let statement =
 `!to_fmap:A->B->B option.
  !null:B.
  !prev next:A.
  !s:B list.
  !head:B.
    (!container:A.
       FINITE (ntp4vc_dll_bst_fmap_domain (to_fmap container)))
    ==>
    ntp4vc_dll_bst_dll
      null (to_fmap prev) (to_fmap next) s head
      (&0:int) (&(LENGTH s):int)
    ==>
    ntp4vc_dll_bst_dll
      null (to_fmap prev) (to_fmap next) s head
      (&0:int) (&(LENGTH s):int) /\
    (let n = (&(LENGTH s):int) - (&0:int) in
     ntp4vc_dll_bst_dll
       null (to_fmap prev) (to_fmap next) s head
       (&0:int) ((&0:int) + n) /\
     (!next1 prev1:A.
      !o1:B.
      !o2:ntp4vc_dll_bst_tree.
        ntp4vc_dll_bst_tree
          null (to_fmap prev1) (to_fmap next1) s o1 o2
          (&0:int) ((&0:int) + n) /\
        ntp4vc_dll_bst_fmap_domain (to_fmap prev1) =
          ntp4vc_dll_bst_fmap_domain (to_fmap prev) /\
        ntp4vc_dll_bst_fmap_domain (to_fmap next1) =
          ntp4vc_dll_bst_fmap_domain (to_fmap next) /\
        (!i:int.
           (&0:int) <= i /\ i < (&0:int)
           ==>
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap prev1) =
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap prev)) /\
        (!i:int.
           (&0:int) + n <= i /\ i < (&(LENGTH s):int)
           ==>
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap prev1) =
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap prev)) /\
        (!i:int.
           (&0:int) <= i /\ i < (&0:int)
           ==>
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap next1) =
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap next)) /\
        (!i:int.
           (&0:int) + n <= i /\ i < (&(LENGTH s):int)
           ==>
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap next1) =
           ntp4vc_dll_bst_fmap_lookup
             (ntp4vc_dll_bst_nth s i) (to_fmap next)) /\
        ((&0:int) < n
         ==>
         (let h = ntp4vc_dll_bst_height o2 in
          ntp4vc_dll_bst_int_power
            (&2:int) (h - (&1:int)) <= n /\
          n < ntp4vc_dll_bst_int_power (&2:int) h))
        ==>
        ntp4vc_dll_bst_tree
          null (to_fmap prev1) (to_fmap next1) s o1 o2
          (&0:int) (&(LENGTH s):int) /\
        ntp4vc_dll_bst_size o2 = (&(LENGTH s):int) /\
        ntp4vc_dll_bst_inorder s o2 = s /\
        ((&0:int) < (&(LENGTH s):int)
         ==>
         (let h = ntp4vc_dll_bst_height o2 in
          ntp4vc_dll_bst_int_power
            (&2:int) (h - (&1:int)) <= (&(LENGTH s):int) /\
          (&(LENGTH s):int) <
            ntp4vc_dll_bst_int_power (&2:int) h))))`;;
