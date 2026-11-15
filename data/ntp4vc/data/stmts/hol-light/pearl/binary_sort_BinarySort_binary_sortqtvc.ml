(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/binary_sort_BinarySort_binary_sortqtvc:
  the binary-insertion-sort verification condition for loop invariants,
  midpoint selection by computer integer division, array shifting and update,
  sortedness, and whole-array permutation. This file contains no proof.
*)

let binary_sort_nth = new_definition
 `binary_sort_nth (a:int list) (i:int) =
    if i < (&0:int) then
      (&0:int)
    else if num_of_int i < LENGTH a then
      EL (num_of_int i) a
    else
      (&0:int)`;;

let binary_sort_update =
  new_recursive_definition list_RECURSION
   `(!n x.
       binary_sort_update ([]:int list) n x = []) /\
    (!h t n x.
       binary_sort_update (CONS h t) n x =
       if n = 0 then CONS x t
       else CONS h (binary_sort_update t (PRE n) x))`;;

let binary_sort_cdiv = new_definition
 `binary_sort_cdiv (n:int) (d:int) =
    if (&0:int) <= n then
      if (&0:int) <= d then n div d else --(n div --d)
    else
      if (&0:int) <= d then --(--n div d) else --n div --d`;;

let binary_sort_permut_sub_prime = new_definition
 `binary_sort_permut_sub_prime
    (a1:int list) (a2:int list) (l:num) (u:num) <=>
    LENGTH a1 = LENGTH a2 /\
    (!q:num.
       q < l /\ q < LENGTH a1
       ==> EL q a1 = EL q a2) /\
    (!q:num.
       u <= q /\ q < LENGTH a1
       ==> EL q a1 = EL q a2) /\
    (!v:int.
       CARD {q:num |
               l <= q /\ q < u /\ q < LENGTH a1 /\ EL q a1 = v} =
       CARD {q:num |
               l <= q /\ q < u /\ q < LENGTH a2 /\ EL q a2 = v})`;;

let statement =
 `!a:int list.
    let o1 = (&(LENGTH a):int) - (&1:int) in
    (((&1:int) <= o1 + (&1:int)
      ==>
      ((!i j:int.
          (&0:int) <= i /\ i <= j /\ j < (&1:int)
          ==> binary_sort_nth a i <= binary_sort_nth a j) /\
       binary_sort_permut_sub_prime a a 0 (LENGTH a)) /\
      (!a1:int list.
         LENGTH a1 = LENGTH a
         ==>
         ((!k:int.
             (((&1:int) <= k /\ k <= o1) /\
              (!i j:int.
                 (&0:int) <= i /\ i <= j /\ j < k
                 ==> binary_sort_nth a1 i <= binary_sort_nth a1 j) /\
              binary_sort_permut_sub_prime
                a a1 0 (LENGTH a1))
             ==>
             ((&0:int) <= k /\ k < (&(LENGTH a1):int)) /\
             (let v = binary_sort_nth a1 k in
              ((((&0:int) <= (&0:int) /\
                 (&0:int) <= k /\
                 k <= k) /\
                (!i:int.
                   (&0:int) <= i /\ i < (&0:int)
                   ==> binary_sort_nth a1 i <= v) /\
                (!i:int.
                   k <= i /\ i < k
                   ==> v < binary_sort_nth a1 i)) /\
               (!right1 left1:int.
                  (((&0:int) <= left1 /\
                    left1 <= right1 /\
                    right1 <= k) /\
                   (!i:int.
                      (&0:int) <= i /\ i < left1
                      ==> binary_sort_nth a1 i <= v) /\
                   (!i:int.
                      right1 <= i /\ i < k
                      ==> v < binary_sort_nth a1 i))
                  ==>
                  if left1 < right1 then
                    ~((&2:int) = (&0:int)) /\
                    (let mid =
                       left1 +
                       binary_sort_cdiv
                         (right1 - left1) (&2:int) in
                     ((&0:int) <= mid /\
                      mid < (&(LENGTH a1):int)) /\
                     (if v < binary_sort_nth a1 mid then
                        (((&0:int) <= right1 - left1 /\
                          mid - left1 < right1 - left1) /\
                         ((&0:int) <= left1 /\
                          left1 <= mid /\
                          mid <= k) /\
                         (!i:int.
                            (&0:int) <= i /\ i < left1
                            ==> binary_sort_nth a1 i <= v) /\
                         (!i:int.
                            mid <= i /\ i < k
                            ==> v < binary_sort_nth a1 i))
                      else
                        (((&0:int) <= right1 - left1 /\
                          right1 - (mid + (&1:int)) <
                          right1 - left1) /\
                         ((&0:int) <= mid + (&1:int) /\
                          mid + (&1:int) <= right1 /\
                          right1 <= k) /\
                         (!i:int.
                            (&0:int) <= i /\
                            i < mid + (&1:int)
                            ==> binary_sort_nth a1 i <= v) /\
                         (!i:int.
                            right1 <= i /\ i < k
                            ==> v < binary_sort_nth a1 i))))
                  else
                    let o2 = k - left1 in
                    let o3 = left1 + (&1:int) in
                    ((((&0:int) <= left1 /\
                       (&0:int) <= o2 /\
                       left1 + o2 <= (&(LENGTH a1):int)) /\
                      (&0:int) <= o3 /\
                      o3 + o2 <= (&(LENGTH a1):int)) /\
                     (!a2:int list.
                        LENGTH a2 = LENGTH a1
                        ==>
                        ((!i:int.
                            (((&0:int) <= i /\ i < o3) \/
                             (o3 + o2 <= i /\
                              i < (&(LENGTH a2):int)))
                            ==> binary_sort_nth a2 i =
                                binary_sort_nth a1 i) /\
                         (!i:int.
                            o3 <= i /\ i < o3 + o2
                            ==> binary_sort_nth a2 i =
                                binary_sort_nth
                                  a1 (left1 + i - o3)))
                        ==>
                        ((&0:int) <= left1 /\
                         left1 < (&(LENGTH a2):int)) /\
                        (LENGTH
                           (binary_sort_update
                              a2 (num_of_int left1) v) =
                         LENGTH a2
                         ==>
                         (!r:int.
                            binary_sort_nth
                              (binary_sort_update
                                 a2 (num_of_int left1) v) r =
                            if r = left1 then v
                            else binary_sort_nth a2 r)
                         ==>
                         (!i j:int.
                            (&0:int) <= i /\
                            i <= j /\
                            j < k + (&1:int)
                            ==> binary_sort_nth
                                  (binary_sort_update
                                     a2 (num_of_int left1) v) i <=
                                binary_sort_nth
                                  (binary_sort_update
                                     a2 (num_of_int left1) v) j) /\
                         binary_sort_permut_sub_prime
                           a
                           (binary_sort_update
                              a2 (num_of_int left1) v)
                           0
                           (LENGTH
                              (binary_sort_update
                                 a2 (num_of_int left1) v)))))))))) /\
          (((!i j:int.
               (&0:int) <= i /\
               i <= j /\
               j < o1 + (&1:int)
               ==> binary_sort_nth a1 i <=
                   binary_sort_nth a1 j) /\
             binary_sort_permut_sub_prime
               a a1 0 (LENGTH a1))
            ==>
            (!i j:int.
               (&0:int) <= i /\
               i <= j /\
               j < (&(LENGTH a1):int)
               ==> binary_sort_nth a1 i <=
                   binary_sort_nth a1 j) /\
            binary_sort_permut_sub_prime
              a a1 0 (LENGTH a1))))
     /\
     (o1 + (&1:int) < (&1:int)
      ==>
      (!i j:int.
         (&0:int) <= i /\
         i <= j /\
         j < (&(LENGTH a):int)
         ==> binary_sort_nth a i <= binary_sort_nth a j) /\
      binary_sort_permut_sub_prime a a 0 (LENGTH a)))`;;
