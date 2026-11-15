(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/verifythis_2019_ghc_sort_Top_cutpointsqtvc: the verification
  condition for constructing cutpoints that partition a nonempty integer
  array into ordered monotonic segments. This file contains no proof.
*)

let ghc_cut_index = new_definition
 `ghc_cut_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ghc_cut_nth = new_definition
 `ghc_cut_nth (xs:int list) (i:int) =
    if ghc_cut_index i < LENGTH xs
    then EL (ghc_cut_index i) xs
    else (&0:int)`;;

let ghc_cut_seq = new_definition
 `ghc_cut_seq (list_seq:int list) = REVERSE list_seq`;;

let ghc_cut_seq_nth = new_definition
 `ghc_cut_seq_nth (list_seq:int list) (i:int) =
    ghc_cut_nth (ghc_cut_seq list_seq) i`;;

let ghc_cut_last = new_definition
 `ghc_cut_last (list_seq:int list) =
    ghc_cut_seq_nth
      list_seq
      ((&(LENGTH (ghc_cut_seq list_seq)):int) - (&1:int))`;;

let ghc_cut_run = new_definition
 `ghc_cut_run
    (s:int list) (lower:int) (upper:int) <=>
    (!z1 z2:int.
       lower <= z1 /\ z1 < z2 /\ z2 < upper
       ==> ghc_cut_nth s z1 < ghc_cut_nth s z2) \/
    (!z1 z2:int.
       lower <= z1 /\ z1 < z2 /\ z2 < upper
       ==> ghc_cut_nth s z2 <= ghc_cut_nth s z1)`;;

let ghc_cut_all_segments = new_definition
 `ghc_cut_all_segments (s:int list) (list_seq:int list) <=>
    !k:int.
      (&0:int) <= k /\
      k < (&(LENGTH (ghc_cut_seq list_seq)):int) - (&1:int)
      ==>
      ghc_cut_run
        s
        (ghc_cut_seq_nth list_seq k)
        (ghc_cut_seq_nth list_seq (k + (&1:int)))`;;

let ghc_cut_seq_sorted = new_definition
 `ghc_cut_seq_sorted (list_seq:int list) <=>
    !i j:int.
      (&0:int) <= i /\
      i < j /\
      j < (&(LENGTH (ghc_cut_seq list_seq)):int)
      ==>
      ghc_cut_seq_nth list_seq i <=
      ghc_cut_seq_nth list_seq j`;;

let ghc_cut_list_bounds = new_definition
 `ghc_cut_list_bounds (list_seq:int list) (upper:int) <=>
    !z:int.
      MEM z list_seq
      ==> (&0:int) <= z /\ z <= upper`;;

let ghc_cut_eqb = new_definition
 `ghc_cut_eqb (b1:bool) (b2:bool) = (b1 <=> b2)`;;

let ghc_cut_lt_bool = new_definition
 `ghc_cut_lt_bool (left:int) (right:int) = (left < right)`;;

let ghc_cut_current_state = new_definition
 `ghc_cut_current_state
    (s:int list) (n:int) (cut:int list) <=>
    let last = ghc_cut_last cut in
    ((&0:int) < last + (&1:int) /\
     last + (&1:int) <= n + (&1:int)) /\
    (&0:int) < (&(LENGTH (ghc_cut_seq cut)):int) /\
    ghc_cut_seq_nth cut (&0:int) = (&0:int) /\
    ghc_cut_list_bounds cut n /\
    ghc_cut_all_segments s cut /\
    ghc_cut_seq_sorted cut`;;

let ghc_cut_final_state = new_definition
 `ghc_cut_final_state (s:int list) (list_seq:int list) <=>
    ghc_cut_seq_nth list_seq (&0:int) = (&0:int) /\
    ghc_cut_last list_seq = (&(LENGTH s):int) /\
    (&2:int) <= (&(LENGTH list_seq):int) /\
    ghc_cut_list_bounds list_seq (&(LENGTH s):int) /\
    ghc_cut_all_segments s list_seq /\
    ghc_cut_seq_sorted list_seq`;;

let ghc_cut_next_state = new_definition
 `ghc_cut_next_state
    (s:int list) (n:int) (cut:int list) (y:int)
    (next:int list) <=>
    let last = ghc_cut_last cut in
    ((&0:int) <= n - (last + (&1:int)) /\
     n - (y + (&1:int)) < n - (last + (&1:int))) /\
    ((&0:int) < y + (&1:int) /\
     y + (&1:int) <= n + (&1:int)) /\
    (&0:int) < (&(LENGTH (ghc_cut_seq next)):int) /\
    ghc_cut_seq_nth next (&0:int) = (&0:int) /\
    ghc_cut_last next = y /\
    ghc_cut_list_bounds next n /\
    ghc_cut_all_segments s next /\
    ghc_cut_seq_sorted next`;;

let ghc_cut_all_next_records = new_definition
 `ghc_cut_all_next_records
    (s:int list) (n:int) (cut:int list) (y:int) <=>
    !next:int list.
      next = CONS y cut
      ==> ghc_cut_next_state s n cut y next`;;

let ghc_cut_o2_antecedent = new_definition
 `ghc_cut_o2_antecedent
    (s:int list) (cut:int list) (y:int) (o2:bool) <=>
    if y < (&(LENGTH s):int) then
      let o3 =
        ghc_cut_lt_bool
          (ghc_cut_nth s (y - (&1:int)))
          (ghc_cut_nth s y) in
      let baseline =
        ghc_cut_lt_bool
          (ghc_cut_nth s (ghc_cut_last cut))
          (ghc_cut_nth s (ghc_cut_last cut + (&1:int))) in
      o2 = ghc_cut_eqb o3 baseline /\
      (o2 = T <=> o3 = baseline)
    else
      o2 = F`;;

let ghc_cut_o2_true_result = new_definition
 `ghc_cut_o2_true_result
    (s:int list) (n:int) (cut:int list) (y:int) <=>
    let last = ghc_cut_last cut in
    ((&0:int) <= n - y /\
     n - (y + (&1:int)) < n - y) /\
    (last + (&1:int) <= y + (&1:int) /\
     y + (&1:int) <= n) /\
    ghc_cut_run s last (y + (&1:int))`;;

let ghc_cut_o2_result = new_definition
 `ghc_cut_o2_result
    (s:int list) (n:int) (cut:int list) (y:int) (o2:bool) <=>
    if o2 = T then
      ghc_cut_o2_true_result s n cut y
    else
      ghc_cut_all_next_records s n cut y`;;

let ghc_cut_all_o2 = new_definition
 `ghc_cut_all_o2
    (s:int list) (n:int) (cut:int list) (y:int) <=>
    !o2:bool.
      ghc_cut_o2_antecedent s cut y o2
      ==> ghc_cut_o2_result s n cut y o2`;;

let ghc_cut_y_result = new_definition
 `ghc_cut_y_result
    (s:int list) (n:int) (cut:int list) (y:int) <=>
    (y < n
     ==>
     ((&0:int) <= y /\ y < (&(LENGTH s):int)) /\
     ((&0:int) <= y - (&1:int) /\
      y - (&1:int) < (&(LENGTH s):int))) /\
    ghc_cut_all_o2 s n cut y`;;

let ghc_cut_all_y = new_definition
 `ghc_cut_all_y (s:int list) (n:int) (cut:int list) <=>
    !y:int.
      ((ghc_cut_last cut + (&1:int) <= y /\ y <= n) /\
       ghc_cut_run s (ghc_cut_last cut) y)
      ==> ghc_cut_y_result s n cut y`;;

let ghc_cut_continue_inner = new_definition
 `ghc_cut_continue_inner
    (s:int list) (n:int) (cut:int list) <=>
    let last = ghc_cut_last cut in
    (((&0:int) <= last + (&1:int) /\
      last + (&1:int) < (&(LENGTH s):int)) /\
     ((&0:int) <= last /\
      last < (&(LENGTH s):int))) /\
    (((last + (&1:int) <= last + (&1:int)) /\
      last + (&1:int) <= n) /\
     ghc_cut_run s last (last + (&1:int))) /\
    ghc_cut_all_y s n cut`;;

let ghc_cut_all_final_extensions = new_definition
 `ghc_cut_all_final_extensions
    (s:int list) (n:int) (cut:int list) <=>
    !next:int list.
      next = CONS n cut
      ==> ghc_cut_final_state s next`;;

let ghc_cut_current_conclusion = new_definition
 `ghc_cut_current_conclusion
    (s:int list) (n:int) (cut:int list) <=>
    let last = ghc_cut_last cut in
    if last + (&1:int) < n then
      ghc_cut_continue_inner s n cut
    else if last < n then
      ghc_cut_all_final_extensions s n cut
    else
      ghc_cut_final_state s cut`;;

let ghc_cut_all_current_records = new_definition
 `ghc_cut_all_current_records (s:int list) (n:int) <=>
    !cut:int list.
      ghc_cut_current_state s n cut
      ==> ghc_cut_current_conclusion s n cut`;;

let ghc_cut_initial_conclusion = new_definition
 `ghc_cut_initial_conclusion
    (s:int list) (n:int) (initial:int list) <=>
    (&1:int) = (&0:int) + (&1:int) /\
    ((&0:int) < (&1:int) /\
     (&1:int) <= n + (&1:int)) /\
    (&0:int) < (&(LENGTH (ghc_cut_seq initial)):int) /\
    ghc_cut_seq_nth initial (&0:int) = (&0:int) /\
    ghc_cut_last initial = (&0:int) /\
    ghc_cut_list_bounds initial n /\
    ghc_cut_all_segments s initial /\
    ghc_cut_seq_sorted initial /\
    ghc_cut_all_current_records s n`;;

let statement =
 `!s:int list.
    (&0:int) < (&(LENGTH s):int)
    ==>
    let n = (&(LENGTH s):int) in
    !initial:int list.
      initial = CONS (&0:int) []
      ==> ghc_cut_initial_conclusion s n initial`;;
