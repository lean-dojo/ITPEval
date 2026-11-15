(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_YetAnotherInPlaceRev_list_reversal_finalqtvc: the
  final verification condition for in-place linked-list reversal, relating
  forward and reversed list layouts while preserving the memory frame. This
  file contains no proof.
*)

let ntp4vc_yet_another_rev_valid_cells = new_definition
 `ntp4vc_yet_another_rev_valid_cells
    (null:A) (s:int->A) (n:int) <=>
    (!i:int.
       (&0:int) <= i /\ i < n
       ==> ~(s i = null)) /\
    (!i j:int.
       (&0:int) <= i /\ i < n
       ==>
       (&0:int) <= j /\ j < n
       ==>
       ~(i = j)
       ==>
       ~(s i = s j))`;;

let ntp4vc_yet_another_rev_list_lr = new_definition
 `ntp4vc_yet_another_rev_list_lr
    (null:A) (next1:A->A) (s:int->A) (l:A) (lo:int) (hi:int) <=>
    (&0:int) <= lo /\ lo <= hi /\
    (if lo = hi then
       l = null
     else
       l = s lo /\
       next1 (s (hi - (&1:int))) = null /\
       (!k:int.
          lo <= k /\ k < hi - (&1:int)
          ==> next1 (s k) = s (k + (&1:int))))`;;

let ntp4vc_yet_another_rev_list_rl = new_definition
 `ntp4vc_yet_another_rev_list_rl
    (null:A) (next1:A->A) (s:int->A) (l:A) (lo:int) (hi:int) <=>
    (&0:int) <= lo /\ lo <= hi /\
    (if lo = hi then
       l = null
     else
       next1 (s lo) = null /\
       l = s (hi - (&1:int)) /\
       (!k:int.
          lo < k /\ k < hi
          ==> next1 (s k) = s (k - (&1:int))))`;;

let ntp4vc_yet_another_rev_frame = new_definition
 `ntp4vc_yet_another_rev_frame
    (next1:A->A) (next2:A->A) (s:int->A) (n:int) <=>
    !p:A.
      (!i:int.
         (&0:int) <= i /\ i < n
         ==> ~(p = s i))
      ==> next1 p = next2 p`;;

let ntp4vc_yet_another_rev_result = new_definition
 `ntp4vc_yet_another_rev_result (s:int->A) (i:int) =
    s (i + (&1:int))`;;

let ntp4vc_yet_another_rev_fc = new_definition
 `ntp4vc_yet_another_rev_fc (s:int->A) (n:int) (i:int) =
    s (n - (&1:int) - i)`;;

let statement =
 `!null:A.
  !is_list:(A->A)->A->(int->A)->int->bool.
    (!n:int.
     !next1:A->A.
     !l:A.
     !s:int->A.
       (&0:int) <= n
       ==>
       (if n = (&0:int) then
          (is_list next1 l s n <=> l = null)
        else
          (is_list next1 l s n <=>
           (l = s (&0:int) /\ ~(s (&0:int) = null)) /\
           is_list
             next1
             (next1 l)
             (ntp4vc_yet_another_rev_result s)
             (n - (&1:int)))))
    ==>
    !mem1:A->A.
    !s:int->A.
    !n:int.
    !l:A.
      (&0:int) <= n /\ is_list mem1 l s n
      ==>
      (ntp4vc_yet_another_rev_valid_cells null s n /\
       ntp4vc_yet_another_rev_list_lr
         null mem1 s l (&0:int) n) /\
      (!mem3:A->A.
       !r:A.
         ntp4vc_yet_another_rev_list_rl
           null mem3 s r (&0:int) n /\
         ntp4vc_yet_another_rev_frame mem3 mem1 s n
         ==>
         is_list mem3 r (ntp4vc_yet_another_rev_fc s n) n /\
         ntp4vc_yet_another_rev_frame mem3 mem1 s n)`;;
