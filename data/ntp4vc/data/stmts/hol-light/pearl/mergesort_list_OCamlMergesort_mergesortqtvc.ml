(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_mergesortqtvc: the mergesort
  verification condition for returning a sorted permutation of an input list,
  under total-preorder, sortedness, and abstract-prefix specifications. This
  file contains no proof.
*)

let statement =
 `let list_perm =
    \(a1:A list) (a2:A list).
      LENGTH a1 = LENGTH a2 /\
      (!v:A.
         CARD {k:num | k < LENGTH a1 /\ EL k a1 = v} =
         CARD {k:num | k < LENGTH a2 /\ EL k a2 = v}) in
  !le:A->A->bool.
  !sorted:A list->bool.
  !prefix1:int->A list->A list.
  !l:A list.
    (!x:A. le x x)
    ==>
    (!x y z:A. le x y /\ le y z ==> le x z)
    ==>
    (!x y:A. le x y \/ le y x)
    ==>
    sorted ([]:A list)
    ==>
    (!x:A. sorted (CONS x []))
    ==>
    (!x y:A.
     !xs:A list.
       le x y
       ==>
       sorted (CONS y xs)
       ==>
       sorted (CONS x (CONS y xs)))
    ==>
    (!x:A.
     !xs:A list.
       ((!y:A. MEM y xs ==> le x y) /\ sorted xs <=>
        sorted (CONS x xs)))
    ==>
    (!xs1 xs2:A list.
       (sorted xs1 /\
        sorted xs2 /\
        (!x y:A. MEM x xs1 ==> MEM y xs2 ==> le x y) <=>
        sorted (APPEND xs1 xs2)))
    ==>
    (!xs:A list. prefix1 (&0:int) xs = [])
    ==>
    (!n:int.
     !x:A.
     !xs:A list.
       (&0:int) < n
       ==>
       prefix1 n (CONS x xs) =
       CONS x (prefix1 (n - (&1:int)) xs))
    ==>
    let n = (&(LENGTH l):int) in
    (~(n < (&2:int))
     ==>
     (&2:int) <= n /\ n <= (&(LENGTH l):int)) /\
    (!result:A list.
       (if n < (&2:int) then
          result = l
        else
          sorted result /\ list_perm result (prefix1 n l))
       ==>
       sorted result /\ list_perm result l)`;;
