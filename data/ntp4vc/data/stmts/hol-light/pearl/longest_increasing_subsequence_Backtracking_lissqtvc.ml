(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/longest_increasing_subsequence_Backtracking_lissqtvc: the
  backtracking verification condition for constructing a longest strictly
  increasing subsequence. This file contains no proof.
*)

let lis_nth_int = new_definition
 `lis_nth_int (a:int list) (i:int) =
    if i < (&0:int) then
      if a = [] then (&0:int) else EL 0 a
    else if num_of_int i < LENGTH a then
      EL (num_of_int i) a
    else
      (&0:int)`;;

let lis_nth_elt = new_definition
 `lis_nth_elt (a:A list) (i:int) =
    if i < (&0:int) then
      if a = [] then ARB else EL 0 a
    else if num_of_int i < LENGTH a then
      EL (num_of_int i) a
    else
      ARB`;;

let lis_iss = new_definition
 `lis_iss (lt:A->A->bool) (s:int list) (w:A list) <=>
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH s):int)
       ==>
       (&0:int) <= lis_nth_int s i /\
       lis_nth_int s i < (&(LENGTH w):int)) /\
    (!i j:int.
       (&0:int) <= i /\ i < j /\ j < (&(LENGTH s):int)
       ==>
       lis_nth_int s i < lis_nth_int s j /\
       lt
         (lis_nth_elt w (lis_nth_int s i))
         (lis_nth_elt w (lis_nth_int s j)))`;;

let lis_liss = new_definition
 `lis_liss (lt:A->A->bool) (s:int list) (w:A list) <=>
    lis_iss lt s w /\
    (!s':int list. lis_iss lt s' w ==> LENGTH s' <= LENGTH s)`;;

let lis_inner_best = new_definition
 `lis_inner_best
    (lt:A->A->bool) (w:A list) (first:int) (bound:int)
    (s:int list) <=>
    (&0:int) < (&(LENGTH s):int) /\
    lis_nth_int s (&0:int) = first /\
    lis_iss lt s w /\
    (!s':int list.
       lis_iss lt s' w
       ==>
       (&2:int) <= (&(LENGTH s'):int)
       ==>
       lis_nth_int s' (&0:int) = first /\
       first < lis_nth_int s' (&1:int) /\
       lis_nth_int s' (&1:int) < bound
       ==>
       LENGTH s' <= LENGTH s)`;;

let lis_inner_state = new_definition
 `lis_inner_state
    (lt:A->A->bool) (w:A list) (first:int) (bound:int)
    (len:int) (s:int list) <=>
    len = (&(LENGTH s):int) /\
    lis_inner_best lt w first bound s`;;

let lis_exact_best = new_definition
 `lis_exact_best
    (lt:A->A->bool) (w:A list) (first:int) (s:int list) <=>
    (&0:int) < (&(LENGTH s):int) /\
    lis_nth_int s (&0:int) = first /\
    lis_iss lt s w /\
    (!s':int list.
       lis_iss lt s' w
       ==>
       (&1:int) <= (&(LENGTH s'):int)
       ==>
       lis_nth_int s' (&0:int) = first
       ==>
       LENGTH s' <= LENGTH s)`;;

let lis_exact_state = new_definition
 `lis_exact_state
    (lt:A->A->bool) (w:A list) (first:int)
    (len:int) (s:int list) <=>
    len = (&(LENGTH s):int) /\
    lis_exact_best lt w first s`;;

let lis_below_best = new_definition
 `lis_below_best
    (lt:A->A->bool) (w:A list) (bound:int) (s:int list) <=>
    lis_iss lt s w /\
    (!s':int list.
       lis_iss lt s' w
       ==>
       (&1:int) <= (&(LENGTH s'):int)
       ==>
       lis_nth_int s' (&0:int) < bound
       ==>
       LENGTH s' <= LENGTH s)`;;

let lis_extend_result = new_definition
 `lis_extend_result
    (lt:A->A->bool) (w:A list) (first:int) (j:int)
    (len:int) (s:int list) (sj:int list) <=>
    if len < (&1:int) + (&(LENGTH sj):int) then
      let o4 = CONS first sj in
      ((&(LENGTH o4):int) = (&1:int) + (&(LENGTH sj):int) /\
       lis_nth_int o4 (&0:int) = first /\
       (!i1:int.
          (&0:int) < i1 /\ i1 <= (&(LENGTH sj):int)
          ==>
          lis_nth_int o4 i1 =
          lis_nth_int sj (i1 - (&1:int)))
       ==>
       lis_inner_state
         lt w first (j + (&1:int))
         ((&1:int) + (&(LENGTH sj):int)) o4)
    else
      lis_inner_state lt w first (j + (&1:int)) len s`;;

let lis_inner_step = new_definition
 `lis_inner_step
    (lt:A->A->bool) (w:A list) (first:int) (j:int)
    (len:int) (s:int list) <=>
    if lt (lis_nth_elt w first) (lis_nth_elt w j) then
      (((&0:int) <= (&(LENGTH w):int) - first /\
        (&(LENGTH w):int) - j <
          (&(LENGTH w):int) - first) /\
       (&0:int) <= j /\ j < (&(LENGTH w):int)) /\
      (!sj:int list.
         lis_exact_best lt w j sj
         ==>
         lis_extend_result lt w first j len s sj)
    else
      lis_inner_state lt w first (j + (&1:int)) len s`;;

let lis_index_vc = new_definition
 `lis_index_vc (lt:A->A->bool) (w:A list) (i:int) <=>
    let o1 = [i] in
    (&(LENGTH o1):int) = (&1:int) /\
    lis_nth_int o1 (&0:int) = i
    ==>
    let o2 = (&(LENGTH w):int) - (&1:int) in
    let o3 = i + (&1:int) in
    (o3 <= o2 + (&1:int)
     ==>
     lis_inner_state lt w i o3 (&1:int) o1 /\
     (!s:int list.
      !len:int.
        (!j:int.
           (o3 <= j /\ j <= o2) /\
           lis_inner_state lt w i j len s
           ==>
           lis_inner_step lt w i j len s) /\
        (lis_inner_state lt w i (o2 + (&1:int)) len s
         ==>
         lis_exact_state lt w i len s))) /\
    (o2 + (&1:int) < o3
     ==>
     lis_exact_state lt w i (&1:int) o1)`;;

let lis_outer_choice = new_definition
 `lis_outer_choice
    (lt:A->A->bool) (w:A list) (i:int)
    (len:int) (s:int list) (si:int list) <=>
    if len < (&(LENGTH si):int) then
      lis_below_best lt w (i + (&1:int)) si
    else
      len = (&(LENGTH s):int) /\
      lis_below_best lt w (i + (&1:int)) s`;;

let lis_outer_vc = new_definition
 `lis_outer_vc (lt:A->A->bool) (w:A list) <=>
    let o1 = (&(LENGTH w):int) - (&1:int) in
    ((&0:int) <= o1 + (&1:int)
     ==>
     ((&0:int) = (&(LENGTH ([]:int list)):int) /\
      lis_below_best lt w (&0:int) ([]:int list)) /\
     (!s:int list.
      !len:int.
        (!i:int.
           ((&0:int) <= i /\ i <= o1) /\
           len = (&(LENGTH s):int) /\
           lis_below_best lt w i s
           ==>
           ((&0:int) <= i /\ i < (&(LENGTH w):int)) /\
           (!si:int list.
              lis_exact_best lt w i si
              ==>
              lis_outer_choice lt w i len s si)) /\
        (len = (&(LENGTH s):int) /\
         lis_below_best lt w (o1 + (&1:int)) s
         ==>
         len = (&(LENGTH s):int) /\
         lis_liss lt s w))) /\
    (o1 + (&1:int) < (&0:int)
     ==>
     (&0:int) = (&(LENGTH ([]:int list)):int) /\
     lis_liss lt ([]:int list) w)`;;

let statement =
 `!lt:A->A->bool.
    ((!x y z:A. lt x y /\ lt y z ==> lt x z) /\
     (!x y:A. lt x y ==> ~lt y x) /\
     (!x y:A. lt x y \/ lt y x \/ x = y))
    ==>
    !w:A list.
      (!i:int.
         (&0:int) <= i /\ i < (&(LENGTH w):int)
         ==>
         lis_index_vc lt w i) /\
      lis_outer_vc lt w`;;
