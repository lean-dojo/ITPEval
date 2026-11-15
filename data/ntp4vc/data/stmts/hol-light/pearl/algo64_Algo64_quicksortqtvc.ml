(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/algo64_Algo64_quicksortqtvc:
  a quicksort verification condition combining subrange permutation,
  partitioning around the pivot value 42, recursive decrease obligations,
  and sortedness of the recombined integer-list segment. This file contains
  no proof.
*)

let statement =
 `let nth_i =
    \(a:int list) (r:int).
      COND (r < (&0:int))
        (COND (a = []) (&0:int) (EL 0 a))
        (COND (num_of_int r < LENGTH a)
          (EL (num_of_int r) a) (&0:int)) in
  let permut_sub =
    \(a1:int list) (a2:int list) (l:num) (u:num).
      LENGTH a1 = LENGTH a2 /\
      (!k:num.
         k < l /\ k < LENGTH a1
         ==> EL k a1 = EL k a2) /\
      (!k:num.
         u <= k /\ k < LENGTH a1
         ==> EL k a1 = EL k a2) /\
      (!v:int.
         CARD {k:num |
                 l <= k /\ k < u /\ k < LENGTH a1 /\ EL k a1 = v} =
         CARD {k:num |
                 l <= k /\ k < u /\ k < LENGTH a2 /\ EL k a2 = v}) in
  let sorted_sub =
    \(a:int list) (l:int) (u:int).
      !i1 i2:int.
        l <= i1 /\ i1 <= i2 /\ i2 < u
        ==> nth_i a i1 <= nth_i a i2 in
  !m n:int. !a:int list.
    (&0:int) <= m ==>
    m <= n ==>
    n < &(LENGTH a) ==>
    COND (m < n)
      (((&0:int) <= m /\ m < n /\ n < &(LENGTH a)) /\
      (!j i:int. !a1:int list.
         LENGTH a1 = LENGTH a ==>
         (m <= j /\ j < i /\ i <= n) /\
         permut_sub a a1
           (num_of_int m) (num_of_int (n + (&1:int))) /\
         (!r:int.
            m <= r /\ r <= j
            ==> nth_i a1 r <= (&42:int)) /\
         (!r:int.
            j < r /\ r < i
            ==> nth_i a1 r = (&42:int)) /\
         (!r:int.
            i <= r /\ r <= n
            ==> (&42:int) <= nth_i a1 r) ==>
         (((&0:int) <= n - m /\ j - m < n - m) /\
          (&0:int) <= m /\ m <= j /\ j < &(LENGTH a1)) /\
         (!a2:int list.
            LENGTH a2 = LENGTH a1 ==>
            permut_sub a1 a2
              (num_of_int m) (num_of_int (j + (&1:int))) /\
            sorted_sub a2 m (j + (&1:int)) ==>
            (((&0:int) <= n - m /\ n - i < n - m) /\
             (&0:int) <= i /\ i <= n /\ n < &(LENGTH a2)) /\
            (!a3:int list.
               LENGTH a3 = LENGTH a2 ==>
               permut_sub a2 a3
                 (num_of_int i) (num_of_int (n + (&1:int))) /\
               sorted_sub a3 i (n + (&1:int)) ==>
               permut_sub a a3
                 (num_of_int m) (num_of_int (n + (&1:int))) /\
               sorted_sub a3 m (n + (&1:int))))))
      (
      permut_sub a a
        (num_of_int m) (num_of_int (n + (&1:int))) /\
      sorted_sub a m (n + (&1:int)))`;;
