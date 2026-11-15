(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/algo65_Algo65_findqtvc:
  a partition-finding verification condition preserving an integer-list
  subrange permutation and placing the selected index k between values no
  greater and no less than its value. This file contains no proof.
*)

let statement =
 `let nth_i =
    \(a:int list) (r:int).
      if r < (&0:int) then
        if a = [] then (&0:int) else EL 0 a
      else if num_of_int r < LENGTH a then EL (num_of_int r) a
      else (&0:int) in
  let permut_sub =
    \(a1:int list) (a2:int list) (l:num) (u:num).
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
                 l <= q /\ q < u /\ q < LENGTH a2 /\ EL q a2 = v}) in
  let pivoted =
    \(a:int list) (l:int) (p:int) (u:int).
      (!r:int.
         l <= r /\ r <= p
         ==> nth_i a r <= nth_i a p) /\
      (!r:int.
         p <= r /\ r <= u
         ==> nth_i a p <= nth_i a r) in
  let selected =
    \(original:int list) (current:int list)
     (l:int) (p:int) (u:int).
      permut_sub original current
        (num_of_int l) (num_of_int (u + (&1:int))) /\
      pivoted current l p u in
  let partitioned =
    \(original:int list) (current:int list)
     (m:int) (j:int) (i:int) (n:int).
      (m <= j /\ j < i /\ i <= n) /\
      permut_sub original current
        (num_of_int m) (num_of_int (n + (&1:int))) /\
      (!r:int.
         m <= r /\ r <= j
         ==> nth_i current r <= (&42:int)) /\
      (!r:int.
         j < r /\ r < i
         ==> nth_i current r = (&42:int)) /\
      (!r:int.
         i <= r /\ r <= n
         ==> (&42:int) <= nth_i current r) in
  !m k n:int. !a:int list.
    (&0:int) <= m ==>
    m <= k ==>
    k <= n ==>
    n < &(LENGTH a) ==>
    if m < n then
      (((&0:int) <= m /\ m < n /\ n < &(LENGTH a)) /\
       (!j i:int. !a1:int list.
         LENGTH a1 = LENGTH a ==>
         partitioned a a1 m j i n ==>
         (if k <= j then
           (((&0:int) <= n - m /\ j - m < n - m) /\
            (&0:int) <= m /\ m <= k /\ k <= j /\
            j < &(LENGTH a1)) /\
           (!a2:int list.
              LENGTH a2 = LENGTH a1 ==>
              permut_sub a1 a2
                (num_of_int m) (num_of_int (j + (&1:int))) /\
              pivoted a2 m k j ==>
              (if i <= k then
                (((&0:int) <= n - m /\ n - i < n - m) /\
                 (&0:int) <= i /\ i <= k /\ k <= n /\
                 n < &(LENGTH a2)) /\
                (!a3:int list.
                   LENGTH a3 = LENGTH a2 ==>
                   permut_sub a2 a3
                     (num_of_int i) (num_of_int (n + (&1:int))) /\
                   pivoted a3 i k n ==>
                   selected a a3 m k n)
              else
                selected a a2 m k n))
         else
           (if i <= k then
             (((&0:int) <= n - m /\ n - i < n - m) /\
              (&0:int) <= i /\ i <= k /\ k <= n /\
              n < &(LENGTH a1)) /\
             (!a2:int list.
                LENGTH a2 = LENGTH a1 ==>
                permut_sub a1 a2
                  (num_of_int i) (num_of_int (n + (&1:int))) /\
                pivoted a2 i k n ==>
                selected a a2 m k n)
           else
             selected a a1 m k n))))
    else
      selected a a m k n`;;
