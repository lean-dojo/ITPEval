(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/flag2_Flag_swapqtvc: the verification condition for swapping two
  in-bounds entries of a three-color list while preserving all other entries
  and interval occurrence counts. This file contains no proof.
*)

let flag2_swap_color_INDUCT,flag2_swap_color_RECURSION = define_type
  "flag2_swap_color =
     Flag2SwapBlue | Flag2SwapWhite | Flag2SwapRed";;

let flag2_swap_monochrome = new_definition
 `flag2_swap_monochrome
    (a:int->flag2_swap_color) (i:int) (j:int)
    (c:flag2_swap_color) <=>
    !k:int. i <= k /\ k < j ==> a k = c`;;

let flag2_swap_nth = new_definition
 `flag2_swap_nth
    (default:flag2_swap_color) (a:flag2_swap_color list) (i:int) =
    if a = [] then default
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else default`;;

let flag2_swap_update_nat =
  new_recursive_definition list_RECURSION
   `(!n x:flag2_swap_color. flag2_swap_update_nat [] n x = []) /\
    (!h:flag2_swap_color.
     !t:flag2_swap_color list.
     !n:num.
     !x:flag2_swap_color.
       flag2_swap_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (flag2_swap_update_nat t (PRE n) x))`;;

let flag2_swap_update = new_definition
 `flag2_swap_update
    (a:flag2_swap_color list) (i:int) (x:flag2_swap_color) =
    if i < (&0:int)
    then flag2_swap_update_nat a 0 x
    else flag2_swap_update_nat a (num_of_int i) x`;;

let statement =
 `!default:flag2_swap_color.
  !nb_occ:
     (int->flag2_swap_color)->int->int->flag2_swap_color->int.
    (!j i:int.
     !f:int->flag2_swap_color.
     !c:flag2_swap_color.
       nb_occ f i j c =
       (if j <= i then (&0:int)
        else if f (j - (&1:int)) = c
        then (&1:int) + nb_occ f i (j - (&1:int)) c
        else nb_occ f i (j - (&1:int)) c))
    ==>
    !i:int.
    !a:flag2_swap_color list.
    !j:int.
      (&0:int) <= i
      ==>
      i < (&(LENGTH a):int)
      ==>
      (&0:int) <= j
      ==>
      j < (&(LENGTH a):int)
      ==>
      ((&0:int) <= i /\
       i < (&(LENGTH a):int) /\
       (let ai = flag2_swap_nth default a i in
        ((&0:int) <= j /\ j < (&(LENGTH a):int)) /\
        (let aj = flag2_swap_nth default a j in
         ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
         (let a_i = flag2_swap_update a i aj in
          LENGTH a_i = LENGTH a
          ==>
          (\k:int. flag2_swap_nth default a_i k) =
            (\k:int.
               if k = i then aj
               else flag2_swap_nth default a k)
          ==>
          ((&0:int) <= j /\ j < (&(LENGTH a_i):int)) /\
          (let a_ij = flag2_swap_update a_i j ai in
           LENGTH a_ij = LENGTH a_i
           ==>
           (\k:int. flag2_swap_nth default a_ij k) =
             (\k:int.
                if k = j then ai
                else flag2_swap_nth default a_i k)
           ==>
           flag2_swap_nth default a_ij i =
             flag2_swap_nth default a j /\
           flag2_swap_nth default a_ij j =
             flag2_swap_nth default a i /\
           (!k:int.
              ~(k = i) /\ ~(k = j)
              ==> flag2_swap_nth default a_ij k =
                  flag2_swap_nth default a k) /\
           (!k1 k2:int.
            !c:flag2_swap_color.
              (k1 <= i /\ i < k2) /\ k1 <= j /\ j < k2
              ==>
              nb_occ (flag2_swap_nth default a_ij) k1 k2 c =
              nb_occ (flag2_swap_nth default a) k1 k2 c))))))`;;
