(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/patience_PatienceAbstract_play_cardsqtvc: the abstract patience
  solitaire play-cards verification condition, preserving the stack-state
  invariant and the indexed sequence of card values. This file contains no
  proof.
*)

let ntp4vc_patience_state_INDUCT,ntp4vc_patience_state_RECURSION =
  define_type
   "ntp4vc_patience_state =
      NTP4VC_PatienceState
        int int (int->int) (int->int) (int->int->int)
        (int->int#int) (int->int)";;

let ntp4vc_patience_num_stacks =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_num_stacks
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      ns`;;

let ntp4vc_patience_num_elts =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_num_elts
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      ne`;;

let ntp4vc_patience_values =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_values
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      values`;;

let ntp4vc_patience_stack_sizes =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_stack_sizes
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      stack_sizes`;;

let ntp4vc_patience_stacks =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_stacks
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      stacks`;;

let ntp4vc_patience_positions =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_positions
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      positions`;;

let ntp4vc_patience_preds =
  new_recursive_definition ntp4vc_patience_state_RECURSION
   `ntp4vc_patience_preds
      (NTP4VC_PatienceState ns ne values stack_sizes stacks positions preds) =
      preds`;;

let ntp4vc_patience_int_index = new_definition
 `ntp4vc_patience_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_patience_nth = new_definition
 `ntp4vc_patience_nth (xs:A list) (i:int) =
    if ntp4vc_patience_int_index i < LENGTH xs
    then EL (ntp4vc_patience_int_index i) xs
    else ARB`;;

let ntp4vc_patience_function_update = new_definition
 `ntp4vc_patience_function_update (f:A->B) (x:A) (y:B) =
    \z:A. if z = x then y else f z`;;

let ntp4vc_patience_inv = new_definition
 `ntp4vc_patience_inv (s:ntp4vc_patience_state) <=>
    ((&0:int) <= ntp4vc_patience_num_stacks s /\
     ntp4vc_patience_num_stacks s <= ntp4vc_patience_num_elts s) /\
    ((&0:int) < ntp4vc_patience_num_elts s
     ==> (&0:int) < ntp4vc_patience_num_stacks s) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_stacks s
       ==>
       (&1:int) <= ntp4vc_patience_stack_sizes s i /\
       (!j:int.
          (&0:int) <= j /\ j < ntp4vc_patience_stack_sizes s i
          ==>
          (&0:int) <= ntp4vc_patience_stacks s i j /\
          ntp4vc_patience_stacks s i j <
            ntp4vc_patience_num_elts s)) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_elts s
       ==>
       let pos = ntp4vc_patience_positions s i in
       ((&0:int) <= FST pos /\
        FST pos < ntp4vc_patience_num_stacks s) /\
       ((&0:int) <= SND pos /\
        SND pos < ntp4vc_patience_stack_sizes s (FST pos)) /\
       ntp4vc_patience_stacks s (FST pos) (SND pos) = i) /\
    (!is:int.
       (&0:int) <= is /\ is < ntp4vc_patience_num_stacks s
       ==>
       !ip:int.
         (&0:int) <= ip /\ ip < ntp4vc_patience_stack_sizes s is
         ==>
         (is,ip) =
         ntp4vc_patience_positions s (ntp4vc_patience_stacks s is ip)) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_stacks s
       ==>
       !j k:int.
         (&0:int) <= j /\ j < k /\
         k < ntp4vc_patience_stack_sizes s i
         ==>
         ntp4vc_patience_stacks s i j <
         ntp4vc_patience_stacks s i k) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_stacks s
       ==>
       !j k:int.
         (&0:int) <= j /\ j <= k /\
         k < ntp4vc_patience_stack_sizes s i
         ==>
         ntp4vc_patience_values s (ntp4vc_patience_stacks s i k) <=
         ntp4vc_patience_values s (ntp4vc_patience_stacks s i j)) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_elts s
       ==>
       let pred = ntp4vc_patience_preds s i in
       --(&1:int) <= pred /\
       pred < ntp4vc_patience_num_elts s /\
       pred < i /\
       let pos = ntp4vc_patience_positions s i in
       if pred < (&0:int) then
         FST pos = (&0:int)
       else
         ntp4vc_patience_values s pred <
           ntp4vc_patience_values s i /\
         (&0:int) < FST pos /\
         FST (ntp4vc_patience_positions s pred) =
           FST pos - (&1:int))`;;

let ntp4vc_patience_nil_case = new_definition
 `ntp4vc_patience_nil_case
    (s:ntp4vc_patience_state) (input:int list) <=>
    ntp4vc_patience_inv s /\
    ntp4vc_patience_num_elts s =
      ntp4vc_patience_num_elts s + (&(LENGTH input):int) /\
    (!i:int.
       ntp4vc_patience_num_elts s <= i /\
       i < ntp4vc_patience_num_elts s
       ==>
       ntp4vc_patience_values s i =
         ntp4vc_patience_nth input (i - ntp4vc_patience_num_elts s))`;;

let ntp4vc_patience_step_pre = new_definition
 `ntp4vc_patience_step_pre
    (s:ntp4vc_patience_state) (c:int)
    (s1:ntp4vc_patience_state) <=>
    ntp4vc_patience_inv s1 /\
    ntp4vc_patience_num_elts s1 =
      ntp4vc_patience_num_elts s + (&1:int) /\
    ntp4vc_patience_values s1 =
      ntp4vc_patience_function_update
        (ntp4vc_patience_values s)
        (ntp4vc_patience_num_elts s) c`;;

let ntp4vc_patience_tail_pre = new_definition
 `ntp4vc_patience_tail_pre
    (s1:ntp4vc_patience_state) (tail:int list)
    (s2:ntp4vc_patience_state) <=>
    ntp4vc_patience_inv s2 /\
    ntp4vc_patience_num_elts s2 =
      ntp4vc_patience_num_elts s1 + (&(LENGTH tail):int) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_elts s1
       ==>
       ntp4vc_patience_values s2 i =
         ntp4vc_patience_values s1 i) /\
    (!i:int.
       ntp4vc_patience_num_elts s1 <= i /\
       i < ntp4vc_patience_num_elts s2
       ==>
       ntp4vc_patience_values s2 i =
         ntp4vc_patience_nth tail (i - ntp4vc_patience_num_elts s1))`;;

let ntp4vc_patience_final_post = new_definition
 `ntp4vc_patience_final_post
    (s:ntp4vc_patience_state) (input:int list)
    (s2:ntp4vc_patience_state) <=>
    ntp4vc_patience_inv s2 /\
    ntp4vc_patience_num_elts s2 =
      ntp4vc_patience_num_elts s + (&(LENGTH input):int) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_num_elts s
       ==>
       ntp4vc_patience_values s2 i =
         ntp4vc_patience_values s i) /\
    (!i:int.
       ntp4vc_patience_num_elts s <= i /\
       i < ntp4vc_patience_num_elts s2
       ==>
       ntp4vc_patience_values s2 i =
         ntp4vc_patience_nth input (i - ntp4vc_patience_num_elts s))`;;

let ntp4vc_patience_cons_case = new_definition
 `ntp4vc_patience_cons_case
    (s:ntp4vc_patience_state) (input:int list)
    (c:int) (tail:int list) <=>
    ntp4vc_patience_inv s /\
    (!s1:ntp4vc_patience_state.
       ntp4vc_patience_step_pre s c s1
       ==>
       (input = CONS c tail /\ ntp4vc_patience_inv s1) /\
       (!s2:ntp4vc_patience_state.
          ntp4vc_patience_tail_pre s1 tail s2
          ==>
          ntp4vc_patience_final_post s input s2))`;;

let statement =
 `!s:ntp4vc_patience_state.
  !input:int list.
    ntp4vc_patience_inv s
    ==>
    ((input = [] ==> ntp4vc_patience_nil_case s input) /\
     (!c:int.
      !tail:int list.
        input = CONS c tail
        ==>
        ntp4vc_patience_cons_case s input c tail))`;;
