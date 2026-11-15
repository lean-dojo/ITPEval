(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/sieve_Sieve_sieveqtvc: the integer sieve verification condition,
  including array initialization, nested loop invariants and variants, and
  the final primality characterization. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory primeTheory;

val sieve_to_num_def = Define `
  sieve_to_num (z : int) = if z < 0 then 0 else Num z`;

val sieve_get_def = Define `
  sieve_get (xs : bool list) (i : int) =
    if i < 0 then F
    else if sieve_to_num i < LENGTH xs then EL (sieve_to_num i) xs
    else F`;

val sieve_fun_update_def = Define `
  sieve_fun_update (f : 'a -> 'b) (k : 'a) (v : 'b) =
    \q. if q = k then v else f q`;

val sieve_no_factor_lt_def = Define `
  sieve_no_factor_lt (bnd : int) (num : int) <=>
    (1 : int) < num /\
    !k l : int.
      (((1 : int) < l /\ l < bnd) /\ (1 : int) < k) ==>
      ~(num = k * l)`;

val sieve_Sieve_sieveqtvc_statement =
  ``!n : int.
      (1 : int) < n ==>
      (0 : int) <= n /\
      !t : bool list.
        ((!i : int.
            (0 : int) <= i /\ i < n ==>
            sieve_get t i = T) /\
         &(LENGTH t) = n)
        ==>
        let o1 = F
        in
          ((0 : int) <= (0 : int) /\
           (0 : int) < &(LENGTH t)) /\
          (LENGTH (LUPDATE o1 0 t) = LENGTH t ==>
           (\z : int. sieve_get (LUPDATE o1 0 t) z) =
             sieve_fun_update (sieve_get t) (0 : int) o1
           ==>
           let o2 = F
           in
             ((0 : int) <= (1 : int) /\
              (1 : int) < &(LENGTH (LUPDATE o1 0 t))) /\
             (LENGTH (LUPDATE o2 1 (LUPDATE o1 0 t)) =
                LENGTH (LUPDATE o1 0 t)
              ==>
              (\z : int.
                 sieve_get (LUPDATE o2 1 (LUPDATE o1 0 t)) z) =
                sieve_fun_update
                  (sieve_get (LUPDATE o1 0 t))
                  (1 : int)
                  o2
              ==>
              ((((1 : int) < (2 : int) /\ (2 : int) <= n) /\
                (!j : int.
                   (0 : int) <= j /\ j < n ==>
                   (sieve_get
                      (LUPDATE o2 1 (LUPDATE o1 0 t))
                      j = T
                    <=>
                    sieve_no_factor_lt (2 : int) j))) /\
               (!i : int.
                !t1 : bool list.
                  LENGTH t1 =
                    LENGTH (LUPDATE o2 1 (LUPDATE o1 0 t))
                  ==>
                  (((1 : int) < i /\ i <= n) /\
                   (!j : int.
                      (0 : int) <= j /\ j < n ==>
                      (sieve_get t1 j = T <=>
                       sieve_no_factor_lt i j)))
                  ==>
                  if i < n then
                    ((0 : int) <= i /\ i < &(LENGTH t1)) /\
                    if sieve_get t1 i = T then
                      ((((1 : int) < i /\ i <= n) /\
                        (!j : int.
                           (0 : int) <= j /\ j < n ==>
                           (sieve_get t1 j = T
                            <=>
                            sieve_no_factor_lt i j /\
                            (!k : int.
                               (1 : int) < k /\ k < i ==>
                               ~(j = k * i))))) /\
                       (!r : int.
                        !t2 : bool list.
                          LENGTH t2 = LENGTH t1
                          ==>
                          (((1 : int) < r /\ r <= n) /\
                           (!j : int.
                              (0 : int) <= j /\ j < n ==>
                              (sieve_get t2 j = T
                               <=>
                               sieve_no_factor_lt i j /\
                               (!k : int.
                                  (1 : int) < k /\ k < r ==>
                                  ~(j = k * i)))))
                          ==>
                          if r * i < n then
                            let o3 = F
                            in
                              ((0 : int) <= r * i /\
                               r * i < &(LENGTH t2)) /\
                              (LENGTH
                                 (LUPDATE
                                    o3
                                    (sieve_to_num (r * i))
                                    t2) =
                                 LENGTH t2
                               ==>
                               (\z : int.
                                  sieve_get
                                    (LUPDATE
                                       o3
                                       (sieve_to_num (r * i))
                                       t2)
                                    z) =
                                 sieve_fun_update
                                   (sieve_get t2)
                                   (r * i)
                                   o3
                               ==>
                               ((0 : int) <= n - r /\
                                n - (r + (1 : int)) < n - r) /\
                               ((((1 : int) < r + (1 : int) /\
                                   r + (1 : int) <= n) /\
                                  r * i + i = (r + (1 : int)) * i) /\
                                (!j : int.
                                   (0 : int) <= j /\ j < n ==>
                                   (sieve_get
                                      (LUPDATE
                                         o3
                                         (sieve_to_num (r * i))
                                         t2)
                                      j = T
                                    <=>
                                    sieve_no_factor_lt i j /\
                                    (!k : int.
                                       (1 : int) < k /\
                                       k < r + (1 : int)
                                       ==>
                                       ~(j = k * i))))))
                          else
                            ((0 : int) <= n - i /\
                             n - (i + (1 : int)) < n - i) /\
                            ((1 : int) < i + (1 : int) /\
                             i + (1 : int) <= n) /\
                            (!j : int.
                               (0 : int) <= j /\ j < n ==>
                               (sieve_get t2 j = T
                                <=>
                                sieve_no_factor_lt
                                  (i + (1 : int))
                                  j))))
                    else
                      ((0 : int) <= n - i /\
                       n - (i + (1 : int)) < n - i) /\
                      ((1 : int) < i + (1 : int) /\
                       i + (1 : int) <= n) /\
                      (!j : int.
                         (0 : int) <= j /\ j < n ==>
                         (sieve_get t1 j = T
                          <=>
                          sieve_no_factor_lt (i + (1 : int)) j))
                  else
                    &(LENGTH t1) = n /\
                    !i1 : int.
                      (0 : int) <= i1 /\ i1 < n ==>
                      (sieve_get t1 i1 = T <=>
                       prime (sieve_to_num i1))))))``;
