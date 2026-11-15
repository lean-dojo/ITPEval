(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/mergesort_list_OCamlMergesort_sortqtvc: the forward-order
  mergesort verification condition for recursive-call bounds, sortedness,
  and permutation preservation over an abstract list prefix. This file
  contains no proof.
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
  !n:int.
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
    (!k:int.
     !x:A.
     !xs:A list.
       (&0:int) < k
       ==>
       prefix1 k (CONS x xs) =
       CONS x (prefix1 (k - (&1:int)) xs))
    ==>
    (&2:int) <= n
    ==>
    n <= (&(LENGTH l):int)
    ==>
    (if n = (&2:int) then
       ~(l = []) /\ ~(TL l = [])
     else if n = (&3:int) then
       ~(l = []) /\ ~(TL l = []) /\ ~(TL (TL l) = [])
     else
       ~((&2:int) = (&0:int)) /\
       (let n1 = n div (&2:int) in
        let n2 = n - n1 in
        ((&0:int) <= n1 /\ n1 <= (&(LENGTH l):int)) /\
        (!l2:A list.
           l = APPEND (prefix1 n1 l) l2
           ==>
           (((&0:int) <= n /\ n1 < n) /\
            (&2:int) <= n1 /\
            n1 <= (&(LENGTH l):int)) /\
           (!s1:A list.
              sorted (REVERSE s1) /\ list_perm s1 (prefix1 n1 l)
              ==>
              (((&0:int) <= n /\ n2 < n) /\
               (&2:int) <= n2 /\
               n2 <= (&(LENGTH l2):int)) /\
              (!s2:A list.
                 sorted (REVERSE s2) /\
                 list_perm s2 (prefix1 n2 l2)
                 ==>
                 (sorted ([]:A list) /\
                  sorted (REVERSE s1) /\
                  sorted (REVERSE s2)) /\
                 (!x y:A.
                    MEM x ([]:A list) ==> MEM y s1 ==> le y x) /\
                 (!x y:A.
                    MEM x ([]:A list) ==> MEM y s2 ==> le y x)))))) /\
    (!result:A list.
       (if n = (&2:int) then
          if ~(l = []) /\ ~(TL l = []) then
            let x1 = HD l in
            let x2 = HD (TL l) in
            if le x1 x2 then
              result = CONS x1 (CONS x2 [])
            else
              result = CONS x2 (CONS x1 [])
          else
            F
        else if n = (&3:int) then
          if ~(l = []) /\ ~(TL l = []) /\ ~(TL (TL l) = []) then
            let x1 = HD l in
            let x2 = HD (TL l) in
            let x3 = HD (TL (TL l)) in
            if le x1 x2 then
              if le x2 x3 then
                result = CONS x1 (CONS x2 (CONS x3 []))
              else if le x1 x3 then
                result = CONS x1 (CONS x3 (CONS x2 []))
              else
                result = CONS x3 (CONS x1 (CONS x2 []))
            else if le x1 x3 then
              result = CONS x2 (CONS x1 (CONS x3 []))
            else if le x2 x3 then
              result = CONS x2 (CONS x3 (CONS x1 []))
            else
              result = CONS x3 (CONS x2 (CONS x1 []))
          else
            F
        else
          let n1 = n div (&2:int) in
          ?l2:A list.
            l = APPEND (prefix1 n1 l) l2 /\
            (?s1:A list.
               (sorted (REVERSE s1) /\
                list_perm s1 (prefix1 n1 l)) /\
               (?s2:A list.
                  (sorted (REVERSE s2) /\
                   list_perm s2 (prefix1 (n - n1) l2)) /\
                  sorted result /\
                  list_perm
                    result
                    (APPEND (APPEND ([]:A list) s1) s2))))
        ==>
        sorted result /\
        list_perm result (prefix1 n l))`;;
