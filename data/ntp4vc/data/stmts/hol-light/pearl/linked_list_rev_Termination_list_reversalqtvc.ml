(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linked_list_rev_Termination_list_reversalqtvc: the linked-list
  reversal termination verification condition over finite memory, ranks,
  seen-cell counts, and a lexicographic decrease. This file contains no proof.
*)

let ntp4vc_linked_list_rev_range = new_definition
 `ntp4vc_linked_list_rev_range (i:int) (n:int) <=>
    (&0:int) <= i /\ i < n`;;

let ntp4vc_linked_list_rev_valid_cells = new_definition
 `ntp4vc_linked_list_rev_valid_cells
    (null:A) (s:int->A) (n:int) <=>
    (!i:int.
       ntp4vc_linked_list_rev_range i n
       ==> ~(s i = null)) /\
    (!i j:int.
       ntp4vc_linked_list_rev_range i n
       ==> ntp4vc_linked_list_rev_range j n
       ==> ~(i = j)
       ==> ~(s i = s j))`;;

let ntp4vc_linked_list_rev_inside_memory = new_definition
 `ntp4vc_linked_list_rev_inside_memory
    (null:A) (s:int->A) (n:int) (l:A) <=>
    l = null \/
    ?i:int. ntp4vc_linked_list_rev_range i n /\ l = s i`;;

let ntp4vc_linked_list_rev_finite_memory = new_definition
 `ntp4vc_linked_list_rev_finite_memory
    (null:A) (s:int->A) (n:int) (next:A->A) <=>
    !i:int.
      ntp4vc_linked_list_rev_range i n
      ==>
      ntp4vc_linked_list_rev_inside_memory null s n (next (s i))`;;

let ntp4vc_linked_list_rev_function_update = new_definition
 `ntp4vc_linked_list_rev_function_update
    (f:A->B) (x:A) (y:B) =
    \z:A. if z = x then y else f z`;;

let ntp4vc_linked_list_rev_seen = new_definition
 `ntp4vc_linked_list_rev_seen
    (s:int->A) (idx:A->int) (lo:int) (hi:int) =
    (&(CARD
       {i:int |
          lo <= i /\ i < hi /\ (&0:int) < idx (s i)}):int)`;;

let ntp4vc_linked_list_rev_initial_marker = new_definition
 `ntp4vc_linked_list_rev_initial_marker (null:A) (p:A) =
    if p = null then (&0:int) else --(&1:int)`;;

let ntp4vc_linked_list_rev_rank_bounds = new_definition
 `ntp4vc_linked_list_rev_rank_bounds
    (s:int->A) (n:int) (idx:A->int) (upper:int) <=>
    !i:int.
      ntp4vc_linked_list_rev_range i n
      ==>
      --(&1:int) <= idx (s i) /\ idx (s i) <= upper`;;

let ntp4vc_linked_list_rev_zero_iff_null = new_definition
 `ntp4vc_linked_list_rev_zero_iff_null
    (null:A) (idx:A->int) <=>
    !p:A. (idx p = (&0:int) <=> p = null)`;;

let ntp4vc_linked_list_rev_chain_condition = new_definition
 `ntp4vc_linked_list_rev_chain_condition
    (s:int->A) (n:int) (next:A->A) (idx:A->int)
    (r:A) (l:A) (upper:int) <=>
    if idx l = --(&1:int) then
      idx r = upper /\
      (!i:int.
         ntp4vc_linked_list_rev_range i n
         ==> (&0:int) < idx (s i)
         ==> idx (next (s i)) = idx (s i) - (&1:int))
    else
      !i:int.
        ntp4vc_linked_list_rev_range i n
        ==> (&0:int) < idx (s i) /\ idx (s i) <= idx l
        ==> idx (next (s i)) = idx (s i) - (&1:int)`;;

let ntp4vc_linked_list_rev_loop_invariant = new_definition
 `ntp4vc_linked_list_rev_loop_invariant
    (null:A) (s:int->A) (n:int) (next:A->A)
    (idx:A->int) (r:A) (l:A) <=>
    let count = ntp4vc_linked_list_rev_seen s idx (&0:int) n in
    ntp4vc_linked_list_rev_inside_memory null s n l /\
    ntp4vc_linked_list_rev_inside_memory null s n r /\
    ntp4vc_linked_list_rev_finite_memory null s n next /\
    (&0:int) <= count /\
    ntp4vc_linked_list_rev_rank_bounds s n idx count /\
    ntp4vc_linked_list_rev_zero_iff_null null idx /\
    ntp4vc_linked_list_rev_chain_condition
      s n next idx r l count`;;

let ntp4vc_linked_list_rev_initial_state = new_definition
 `ntp4vc_linked_list_rev_initial_state
    (null:A) (s:int->A) (n:int) (l:A) (mem1:A->A) <=>
    let idx = ntp4vc_linked_list_rev_initial_marker null in
    let count = ntp4vc_linked_list_rev_seen s idx (&0:int) n in
    ntp4vc_linked_list_rev_inside_memory null s n l /\
    ntp4vc_linked_list_rev_inside_memory null s n null /\
    ntp4vc_linked_list_rev_finite_memory null s n mem1 /\
    ((&0:int) = count /\ (&0:int) <= count) /\
    ntp4vc_linked_list_rev_rank_bounds s n idx (&0:int) /\
    ntp4vc_linked_list_rev_zero_iff_null null idx /\
    ntp4vc_linked_list_rev_chain_condition
      s n mem1 idx null l (&0:int)`;;

let ntp4vc_linked_list_rev_updated_post = new_definition
 `ntp4vc_linked_list_rev_updated_post
    (null:A) (s:int->A) (n:int) (idx:A->int)
    (r:A) (l1:A) (mem3:A->A) <=>
    let count = ntp4vc_linked_list_rev_seen s idx (&0:int) n in
    let next_count = count + (&1:int) in
    let updated_idx =
      ntp4vc_linked_list_rev_function_update idx l1 next_count in
    let updated_mem =
      ntp4vc_linked_list_rev_function_update mem3 l1 r in
    let updated_seen =
      ntp4vc_linked_list_rev_seen s updated_idx (&0:int) n in
    ~(l1 = null) /\
    ~(l1 = null) /\
    (((&0:int) <= n - count /\
      n - next_count < n - count) \/
     (n - count = n - next_count /\
      (&0:int) <= (&1:int) + idx l1 /\
      (&1:int) + updated_idx (mem3 l1) <
      (&1:int) + idx l1)) /\
    ntp4vc_linked_list_rev_inside_memory null s n (mem3 l1) /\
    ntp4vc_linked_list_rev_inside_memory null s n l1 /\
    ntp4vc_linked_list_rev_finite_memory null s n updated_mem /\
    (next_count = updated_seen /\ (&0:int) <= updated_seen) /\
    ntp4vc_linked_list_rev_rank_bounds s n updated_idx next_count /\
    ntp4vc_linked_list_rev_zero_iff_null null updated_idx /\
    ntp4vc_linked_list_rev_chain_condition
      s n updated_mem updated_idx l1 (mem3 l1) next_count`;;

let ntp4vc_linked_list_rev_updated_case = new_definition
 `ntp4vc_linked_list_rev_updated_case
    (null:A) (s:int->A) (n:int) (idx:A->int)
    (r:A) (l1:A) (mem3:A->A) <=>
    let count = ntp4vc_linked_list_rev_seen s idx (&0:int) n in
    let updated_idx =
      ntp4vc_linked_list_rev_function_update
        idx l1 (count + (&1:int)) in
    ntp4vc_linked_list_rev_valid_cells null s n /\
    ntp4vc_linked_list_rev_inside_memory null s n l1 /\
    ~(l1 = null) /\
    idx l1 = --(&1:int) /\
    (&0:int) <= count /\
    (ntp4vc_linked_list_rev_seen s updated_idx (&0:int) n =
       (&1:int) + count
     ==>
     ntp4vc_linked_list_rev_updated_post
       null s n idx r l1 mem3)`;;

let ntp4vc_linked_list_rev_nonupdated_case = new_definition
 `ntp4vc_linked_list_rev_nonupdated_case
    (null:A) (s:int->A) (n:int) (idx:A->int)
    (r:A) (l1:A) (mem3:A->A) <=>
    let count = ntp4vc_linked_list_rev_seen s idx (&0:int) n in
    let updated_mem =
      ntp4vc_linked_list_rev_function_update mem3 l1 r in
    ~(l1 = null) /\
    ~(l1 = null) /\
    (((&0:int) <= n - count /\
      n - count < n - count) \/
     ((&0:int) <= (&1:int) + idx l1 /\
      (&1:int) + idx (mem3 l1) < (&1:int) + idx l1)) /\
    ntp4vc_linked_list_rev_inside_memory null s n (mem3 l1) /\
    ntp4vc_linked_list_rev_inside_memory null s n l1 /\
    ntp4vc_linked_list_rev_finite_memory null s n updated_mem /\
    ntp4vc_linked_list_rev_loop_invariant
      null s n updated_mem idx l1 (mem3 l1)`;;

let statement =
 `!null:A.
  !mem1:A->A.
  !s:int->A.
  !n:int.
  !l:A.
    (&0:int) <= n /\
    ntp4vc_linked_list_rev_valid_cells null s n /\
    ntp4vc_linked_list_rev_finite_memory null s n mem1 /\
    ntp4vc_linked_list_rev_inside_memory null s n l
    ==>
    ntp4vc_linked_list_rev_initial_state null s n l mem1 /\
    (!idx:A->int.
     !r:A.
     !l1:A.
     !mem3:A->A.
       ntp4vc_linked_list_rev_loop_invariant
         null s n mem3 idx r l1
       ==>
       ~(l1 = null)
       ==>
       if idx l1 = --(&1:int) then
         ntp4vc_linked_list_rev_updated_case
           null s n idx r l1 mem3
       else
         ntp4vc_linked_list_rev_nonupdated_case
           null s n idx r l1 mem3)`;;
