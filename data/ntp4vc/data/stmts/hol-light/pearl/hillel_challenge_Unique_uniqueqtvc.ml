(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/hillel_challenge_Unique_uniqueqtvc: the list-uniquification
  verification condition, including finite-map domain tracking, prefix
  membership, pairwise distinctness, list update, and final result extraction.
  This file contains no proof.
*)

let unique_nth = new_definition
 `unique_nth (a:int list) (i:int) =
    if a = [] then (&0:int)
    else if i < (&0:int) then EL 0 a
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else (&0:int)`;;

let unique_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:int. unique_update_nat [] n x = []) /\
    (!h:int. !t:int list. !n:num. !x:int.
       unique_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (unique_update_nat t (PRE n) x))`;;

let unique_update = new_definition
 `unique_update (a:int list) (i:int) (x:int) =
    if i < (&0:int)
    then unique_update_nat a 0 x
    else unique_update_nat a (num_of_int i) x`;;

let unique_mem = new_definition
 `unique_mem (x:int) (a:int list) (i:int) <=>
    ?j:int.
      ((&0:int) <= j /\ j < i) /\
      unique_nth a j = x`;;

let unique_distinct = new_definition
 `unique_distinct (a:int list) (len:int) <=>
    !i j:int.
      (&0:int) <= i /\ i < j /\ j < len
      ==> ~(unique_nth a i = unique_nth a j)`;;

let unique_prefix = new_definition
 `unique_prefix
    (a:int list) (res:int list) (h:int->bool) (i:int) (len:int) <=>
    (!x:int. unique_mem x a i <=> x IN h) /\
    (!x:int. unique_mem x a i <=> unique_mem x res len) /\
    unique_distinct res len`;;

let unique_invariant = new_definition
 `unique_invariant
    (a:int list) (res:int list) (h:int->bool) (i:int) (len:int) <=>
    ((&0:int) <= len /\ len <= i) /\
    unique_prefix a res h i len`;;

let unique_postcondition = new_definition
 `unique_postcondition (a:int list) (result:int list) <=>
    (!x:int.
       unique_mem x result (&(LENGTH result):int) <=>
       unique_mem x a (&(LENGTH a):int)) /\
    unique_distinct result (&(LENGTH result):int)`;;

let unique_extract =
  new_definition
   `unique_extract (a:int list) (res:int list) (len:int) <=>
      ((&0:int) <= (&0:int) /\
       (&0:int) <= len /\
       (&0:int) + len <= (&(LENGTH res):int)) /\
      (!result:int list.
         (&(LENGTH result):int) = len /\
         (!i:int.
            (&0:int) <= i /\ i < len
            ==> unique_nth result i =
                unique_nth res ((&0:int) + i))
         ==> unique_postcondition a result)`;;

let unique_step = new_definition
 `unique_step
    (a:int list) (o1:int) (len:int) (res1:int list)
    (h1:int->bool) (i:int) <=>
    ((((&0:int) <= i /\ i <= o1) /\
      unique_invariant a res1 h1 i len)
     ==>
     (((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
      (if ~(unique_nth a i IN h1) then
         ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
         (!h2:int->bool.
            FINITE h2
            ==> h2 = (unique_nth a i) INSERT h1
            ==> ((&0:int) <= i /\ i < (&(LENGTH a):int)) /\
                (let o2 = unique_nth a i in
                 ((&0:int) <= len /\
                  len < (&(LENGTH res1):int)) /\
                 (LENGTH (unique_update res1 len o2) = LENGTH res1
                  ==> unique_nth (unique_update res1 len o2) =
                      (\k:int.
                         if k = len then o2
                         else unique_nth res1 k)
                  ==> unique_invariant
                        a (unique_update res1 len o2) h2
                        (i + (&1:int)) (len + (&1:int)))))
       else
         unique_invariant
           a res1 h1 (i + (&1:int)) len)))`;;

let statement =
 `!a:int list.
    let n = (&(LENGTH a):int) in
    !h:int->bool.
      FINITE h
      ==> h = ({}:int->bool)
      ==> ((&0:int) <= n /\
           (!res:int list.
              ((!i:int.
                  (&0:int) <= i /\ i < n
                  ==> unique_nth res i = (&0:int)) /\
               (&(LENGTH res):int) = n)
              ==> (let o1 = n - (&1:int) in
                   (((&0:int) <= o1 + (&1:int)
                     ==> (((&0:int) <= (&0:int)) /\
                          unique_prefix a res h (&0:int) (&0:int)) /\
                         (!len:int.
                          !res1:int list.
                          !h1:int->bool.
                            FINITE h1
                            ==> LENGTH res1 = LENGTH res
                            ==> ((!i:int.
                                   unique_step
                                     a o1 len res1 h1 i) /\
                                 (((&0:int) <= len /\
                                   len <= o1 + (&1:int)) /\
                                  unique_prefix
                                    a res1 h1
                                    (o1 + (&1:int)) len
                                  ==> unique_extract a res1 len))))
                    /\
                    (o1 + (&1:int) < (&0:int)
                     ==> ((&0:int) <= (&0:int) /\
                          (&0:int) <= (&0:int) /\
                          (&0:int) + (&0:int) <=
                            (&(LENGTH res):int)) /\
                         (!result:int list.
                            (&(LENGTH result):int) = (&0:int) /\
                            (!i:int.
                               (&0:int) <= i /\ i < (&0:int)
                               ==> unique_nth result i =
                                   unique_nth res ((&0:int) + i))
                            ==> unique_postcondition a result))))))`;;
