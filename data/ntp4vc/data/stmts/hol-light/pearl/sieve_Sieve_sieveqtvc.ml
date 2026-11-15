(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sieve_Sieve_sieveqtvc: the sieve verification condition covering
  initialization, composite marking, nested-loop invariants, termination
  variants, and the final primality characterization. This file contains no
  proof.
*)

needs "Library/prime.ml";;

let sieve_nth = new_definition
 `sieve_nth (a:bool list) (i:int) =
    if a = [] then F
    else if i < (&0:int) then F
    else if num_of_int i < LENGTH a then EL (num_of_int i) a
    else F`;;

let sieve_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num. !x:bool. sieve_update_nat [] n x = []) /\
    (!h:bool. !t:bool list. !n:num. !x:bool.
       sieve_update_nat (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (sieve_update_nat t (PRE n) x))`;;

let sieve_update = new_definition
 `sieve_update (a:bool list) (i:int) (x:bool) =
    if i < (&0:int)
    then a
    else sieve_update_nat a (num_of_int i) x`;;

let sieve_function_update = new_definition
 `sieve_function_update (f:A->B) (i:A) (x:B) =
    \j. if j = i then x else f j`;;

let sieve_no_factor_lt = new_definition
 `sieve_no_factor_lt (bnd:int) (num:int) <=>
    (&1:int) < num /\
    (!k l:int.
       (((&1:int) < l /\ l < bnd) /\ (&1:int) < k)
       ==> ~(num = k * l))`;;

let statement =
 `!n:int.
    (&1:int) < n
    ==>
    (&0:int) <= n /\
    (!t:bool list.
       ((!i:int.
          (&0:int) <= i /\ i < n
          ==> sieve_nth t i = T) /\
        (&(LENGTH t):int) = n)
       ==>
       let o1 = F in
       let t0 = sieve_update t (&0:int) o1 in
       ((&0:int) <= (&0:int) /\
        (&0:int) < (&(LENGTH t):int)) /\
       (LENGTH t0 = LENGTH t
        ==>
        (\r:int. sieve_nth t0 r) =
          sieve_function_update
            (\r:int. sieve_nth t r) (&0:int) o1
        ==>
        let o2 = F in
        let t01 = sieve_update t0 (&1:int) o2 in
        ((&0:int) <= (&1:int) /\
         (&1:int) < (&(LENGTH t0):int)) /\
        (LENGTH t01 = LENGTH t0
         ==>
         (\r:int. sieve_nth t01 r) =
           sieve_function_update
             (\r:int. sieve_nth t0 r) (&1:int) o2
         ==>
         ((((&1:int) < (&2:int) /\ (&2:int) <= n) /\
           (!j:int.
              (&0:int) <= j /\ j < n
              ==> (sieve_nth t01 j = T <=>
                   sieve_no_factor_lt (&2:int) j))) /\
          (!i:int.
           !t1:bool list.
             LENGTH t1 = LENGTH t01
             ==>
             (((&1:int) < i /\ i <= n) /\
              (!j:int.
                 (&0:int) <= j /\ j < n
                 ==> (sieve_nth t1 j = T <=>
                      sieve_no_factor_lt i j)))
             ==>
             if i < n then
               ((&0:int) <= i /\ i < (&(LENGTH t1):int)) /\
               (if sieve_nth t1 i = T then
                  ((((&1:int) < i /\ i <= n) /\
                    (!j:int.
                       (&0:int) <= j /\ j < n
                       ==> (sieve_nth t1 j = T <=>
                            sieve_no_factor_lt i j /\
                            (!k:int.
                               (&1:int) < k /\ k < i
                               ==> ~(j = k * i))))) /\
                   (!r:int.
                    !t2:bool list.
                      LENGTH t2 = LENGTH t1
                      ==>
                      (((&1:int) < r /\ r <= n) /\
                       (!j:int.
                          (&0:int) <= j /\ j < n
                          ==> (sieve_nth t2 j = T <=>
                               sieve_no_factor_lt i j /\
                               (!k:int.
                                  (&1:int) < k /\ k < r
                                  ==> ~(j = k * i)))))
                      ==>
                      if r * i < n then
                        let o3 = F in
                        let t3 = sieve_update t2 (r * i) o3 in
                        ((&0:int) <= r * i /\
                         r * i < (&(LENGTH t2):int)) /\
                        (LENGTH t3 = LENGTH t2
                         ==>
                         (\q:int. sieve_nth t3 q) =
                           sieve_function_update
                             (\q:int. sieve_nth t2 q) (r * i) o3
                         ==>
                         (((&0:int) <= n - r /\
                           n - (r + (&1:int)) < n - r) /\
                          ((((&1:int) < r + (&1:int) /\
                             r + (&1:int) <= n) /\
                            r * i + i = (r + (&1:int)) * i) /\
                           (!j:int.
                              (&0:int) <= j /\ j < n
                              ==> (sieve_nth t3 j = T <=>
                                   sieve_no_factor_lt i j /\
                                   (!k:int.
                                      (&1:int) < k /\
                                      k < r + (&1:int)
                                      ==> ~(j = k * i)))))))
                      else
                        ((&0:int) <= n - i /\
                         n - (i + (&1:int)) < n - i) /\
                        ((&1:int) < i + (&1:int) /\
                         i + (&1:int) <= n) /\
                        (!j:int.
                           (&0:int) <= j /\ j < n
                           ==> (sieve_nth t2 j = T <=>
                                sieve_no_factor_lt
                                  (i + (&1:int)) j))))
                else
                  ((&0:int) <= n - i /\
                   n - (i + (&1:int)) < n - i) /\
                  ((&1:int) < i + (&1:int) /\
                   i + (&1:int) <= n) /\
                  (!j:int.
                     (&0:int) <= j /\ j < n
                     ==> (sieve_nth t1 j = T <=>
                          sieve_no_factor_lt (i + (&1:int)) j)))
             else
               (&(LENGTH t1):int) = n /\
               (!i1:int.
                  (&0:int) <= i1 /\ i1 < n
                  ==> (sieve_nth t1 i1 = T <=>
                       prime (num_of_int i1))))))))`;;
