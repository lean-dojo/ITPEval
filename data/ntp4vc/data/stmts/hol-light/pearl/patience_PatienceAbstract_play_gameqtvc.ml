(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/patience_PatienceAbstract_play_gameqtvc: the abstract
  patience-solitaire play-game verification condition, preserving the state
  invariant and the descending-loop obligations used to construct a longest
  strictly increasing subsequence. This file contains no proof.
*)

let ntp4vc_patience_game_state_INDUCT,
    ntp4vc_patience_game_state_RECURSION =
  define_type
   "ntp4vc_patience_game_state =
      NTP4VC_PatienceGameState
        int int (int->int) (int->int) (int->int->int)
        (int->int#int) (int->int)";;

let ntp4vc_patience_game_num_stacks =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_num_stacks
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = ns`;;

let ntp4vc_patience_game_num_elts =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_num_elts
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = ne`;;

let ntp4vc_patience_game_values =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_values
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = values`;;

let ntp4vc_patience_game_stack_sizes =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_stack_sizes
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = stack_sizes`;;

let ntp4vc_patience_game_stacks =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_stacks
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = stacks`;;

let ntp4vc_patience_game_positions =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_positions
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = positions`;;

let ntp4vc_patience_game_preds =
  new_recursive_definition ntp4vc_patience_game_state_RECURSION
   `ntp4vc_patience_game_preds
      (NTP4VC_PatienceGameState
        ns ne values stack_sizes stacks positions preds) = preds`;;

let ntp4vc_patience_game_seq_INDUCT,
    ntp4vc_patience_game_seq_RECURSION =
  define_type
   "ntp4vc_patience_game_seq =
      NTP4VC_PatienceGameSeq int (int->A)";;

let ntp4vc_patience_game_seqlen =
  new_recursive_definition ntp4vc_patience_game_seq_RECURSION
   `ntp4vc_patience_game_seqlen
      (NTP4VC_PatienceGameSeq n f:A ntp4vc_patience_game_seq) = n`;;

let ntp4vc_patience_game_seqval =
  new_recursive_definition ntp4vc_patience_game_seq_RECURSION
   `ntp4vc_patience_game_seqval
      (NTP4VC_PatienceGameSeq n f:A ntp4vc_patience_game_seq) = f`;;

let ntp4vc_patience_game_int_index = new_definition
 `ntp4vc_patience_game_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let ntp4vc_patience_game_nth = new_definition
 `ntp4vc_patience_game_nth (xs:A list) (i:int) =
    if ntp4vc_patience_game_int_index i < LENGTH xs
    then EL (ntp4vc_patience_game_int_index i) xs
    else ARB`;;

let ntp4vc_patience_game_update = new_definition
 `ntp4vc_patience_game_update (f:A->B) (x:A) (y:B) =
    \z:A. if z = x then y else f z`;;

let ntp4vc_patience_game_inv = new_definition
 `ntp4vc_patience_game_inv (s:ntp4vc_patience_game_state) <=>
    ((&0:int) <= ntp4vc_patience_game_num_stacks s /\
     ntp4vc_patience_game_num_stacks s <=
       ntp4vc_patience_game_num_elts s) /\
    ((&0:int) < ntp4vc_patience_game_num_elts s
     ==> (&0:int) < ntp4vc_patience_game_num_stacks s) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_game_num_stacks s
       ==>
       (&1:int) <= ntp4vc_patience_game_stack_sizes s i /\
       (!j:int.
          (&0:int) <= j /\
          j < ntp4vc_patience_game_stack_sizes s i
          ==>
          (&0:int) <= ntp4vc_patience_game_stacks s i j /\
          ntp4vc_patience_game_stacks s i j <
            ntp4vc_patience_game_num_elts s)) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_game_num_elts s
       ==>
       let pos = ntp4vc_patience_game_positions s i in
       ((&0:int) <= FST pos /\
        FST pos < ntp4vc_patience_game_num_stacks s) /\
       ((&0:int) <= SND pos /\
        SND pos <
          ntp4vc_patience_game_stack_sizes s (FST pos)) /\
       ntp4vc_patience_game_stacks s (FST pos) (SND pos) = i) /\
    (!is:int.
       (&0:int) <= is /\ is < ntp4vc_patience_game_num_stacks s
       ==>
       !ip:int.
         (&0:int) <= ip /\
         ip < ntp4vc_patience_game_stack_sizes s is
         ==>
         (is,ip) =
           ntp4vc_patience_game_positions s
             (ntp4vc_patience_game_stacks s is ip)) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_game_num_stacks s
       ==>
       !j k:int.
         (&0:int) <= j /\ j < k /\
         k < ntp4vc_patience_game_stack_sizes s i
         ==>
         ntp4vc_patience_game_stacks s i j <
           ntp4vc_patience_game_stacks s i k) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_game_num_stacks s
       ==>
       !j k:int.
         (&0:int) <= j /\ j <= k /\
         k < ntp4vc_patience_game_stack_sizes s i
         ==>
         ntp4vc_patience_game_values s
           (ntp4vc_patience_game_stacks s i k) <=
         ntp4vc_patience_game_values s
           (ntp4vc_patience_game_stacks s i j)) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_game_num_elts s
       ==>
       let pred = ntp4vc_patience_game_preds s i in
       --(&1:int) <= pred /\
       pred < ntp4vc_patience_game_num_elts s /\
       pred < i /\
       let pos = ntp4vc_patience_game_positions s i in
       if pred < (&0:int) then
         FST pos = (&0:int)
       else
         ntp4vc_patience_game_values s pred <
           ntp4vc_patience_game_values s i /\
         (&0:int) < FST pos /\
         FST (ntp4vc_patience_game_positions s pred) =
           FST pos - (&1:int))`;;

let ntp4vc_patience_game_increasing_subsequence = new_definition
 `ntp4vc_patience_game_increasing_subsequence
    (sigma:int ntp4vc_patience_game_seq) (input:int list) <=>
    ((&0:int) <= ntp4vc_patience_game_seqlen sigma /\
     ntp4vc_patience_game_seqlen sigma <=
       (&(LENGTH input):int)) /\
    ((!i:int.
       (&0:int) <= i /\
       i < ntp4vc_patience_game_seqlen sigma
       ==>
       (&0:int) <= ntp4vc_patience_game_seqval sigma i /\
       ntp4vc_patience_game_seqval sigma i <
         (&(LENGTH input):int)) /\
     (!i j:int.
       (&0:int) <= i /\ i < j /\
       j < ntp4vc_patience_game_seqlen sigma
       ==>
       ntp4vc_patience_game_seqval sigma i <
         ntp4vc_patience_game_seqval sigma j)) /\
    (!i j:int.
       (&0:int) <= i /\ i < j /\
       j < ntp4vc_patience_game_seqlen sigma
       ==>
       ntp4vc_patience_game_nth input
         (ntp4vc_patience_game_seqval sigma i) <
       ntp4vc_patience_game_nth input
         (ntp4vc_patience_game_seqval sigma j))`;;

let ntp4vc_patience_game_maximal_subsequence = new_definition
 `ntp4vc_patience_game_maximal_subsequence
    (s:ntp4vc_patience_game_state) (input:int list) <=>
    (?sigma:int ntp4vc_patience_game_seq.
       ntp4vc_patience_game_seqlen sigma =
         ntp4vc_patience_game_num_stacks s /\
       ntp4vc_patience_game_increasing_subsequence sigma input) /\
    (!sigma:int ntp4vc_patience_game_seq.
       ntp4vc_patience_game_increasing_subsequence sigma input
       ==>
       ntp4vc_patience_game_seqlen sigma <=
         ntp4vc_patience_game_num_stacks s)`;;

let ntp4vc_patience_game_loop_invariant = new_definition
 `ntp4vc_patience_game_loop_invariant
    (s:ntp4vc_patience_game_state) (ns:int) (i:int)
    (sequence:int->int) (index:int) <=>
    (--(&1:int) <= index /\
     index < ntp4vc_patience_game_num_elts s) /\
    ((&0:int) <= i
     ==>
     (&0:int) <= index /\
     FST (ntp4vc_patience_game_positions s index) = i) /\
    (i + (&1:int) < ns
     ==> index < sequence (i + (&1:int))) /\
    ((&0:int) <= i /\ i < ns - (&1:int)
     ==>
     ntp4vc_patience_game_values s index <
       ntp4vc_patience_game_values s (sequence (i + (&1:int)))) /\
    (!j:int.
       i < j /\ j < ns
       ==>
       (&0:int) <= sequence j /\
       sequence j < ntp4vc_patience_game_num_elts s) /\
    (!j k:int.
       i < j /\ j < k /\ k < ns
       ==> sequence j < sequence k) /\
    (!j k:int.
       i < j /\ j < k /\ k < ns
       ==>
       ntp4vc_patience_game_values s (sequence j) <
         ntp4vc_patience_game_values s (sequence k))`;;

let ntp4vc_patience_game_loop_preservation = new_definition
 `ntp4vc_patience_game_loop_preservation
    (s:ntp4vc_patience_game_state) (ns:int) (upper:int)
    (sequence:int->int) (index:int) <=>
    !i:int.
      (i <= upper /\ (&0:int) <= i) /\
      ntp4vc_patience_game_loop_invariant s ns i sequence index
      ==>
      ntp4vc_patience_game_loop_invariant
        s ns (i - (&1:int))
        (ntp4vc_patience_game_update sequence i index)
        (ntp4vc_patience_game_preds s index)`;;

let ntp4vc_patience_game_loop_obligations = new_definition
 `ntp4vc_patience_game_loop_obligations
    (s:ntp4vc_patience_game_state) (input:int list)
    (ns:int) (upper:int) <=>
    !sequence:int->int.
    !index:int.
      ntp4vc_patience_game_loop_preservation
        s ns upper sequence index /\
      (ntp4vc_patience_game_loop_invariant
         s ns ((&0:int) - (&1:int)) sequence index
       ==>
       ntp4vc_patience_game_maximal_subsequence s input)`;;

let ntp4vc_patience_game_nonempty_branch = new_definition
 `ntp4vc_patience_game_nonempty_branch
    (s:ntp4vc_patience_game_state) (input:int list) <=>
    let ns = ntp4vc_patience_game_num_stacks s in
    let top_index =
      ntp4vc_patience_game_stacks s (ns - (&1:int))
        (ntp4vc_patience_game_stack_sizes s (ns - (&1:int)) -
         (&1:int)) in
    let empty_sequence = \i:int. --(&1:int) in
    let upper = ns - (&1:int) in
    (((&0:int) - (&1:int) <= upper
      ==>
      ntp4vc_patience_game_loop_invariant
        s ns upper empty_sequence top_index /\
      ntp4vc_patience_game_loop_obligations
        s input ns upper) /\
     (upper < (&0:int) - (&1:int)
      ==>
      ntp4vc_patience_game_maximal_subsequence s input))`;;

let ntp4vc_patience_game_initial_values = new_definition
 `ntp4vc_patience_game_initial_values (i:int) = --(&1:int)`;;

let ntp4vc_patience_game_initial_state = new_definition
 `ntp4vc_patience_game_initial_state =
    NTP4VC_PatienceGameState
      (&0:int)
      (&0:int)
      ntp4vc_patience_game_initial_values
      (\i:int. (&0:int))
      (\i:int. \j:int. --(&1:int))
      (\i:int. (--(&1:int),--(&1:int)))
      (\i:int. --(&1:int))`;;

let ntp4vc_patience_game_final_state_obligation = new_definition
 `ntp4vc_patience_game_final_state_obligation
    (input:int list) (s:ntp4vc_patience_game_state) <=>
    ntp4vc_patience_game_inv s /\
    ntp4vc_patience_game_num_elts s =
      (&0:int) + (&(LENGTH input):int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&0:int)
       ==>
       ntp4vc_patience_game_values s i =
         ntp4vc_patience_game_initial_values i) /\
    (!i:int.
       (&0:int) <= i /\ i < ntp4vc_patience_game_num_elts s
       ==>
       ntp4vc_patience_game_values s i =
         ntp4vc_patience_game_nth input (i - (&0:int)))`;;

let statement =
 `!input:int list.
    ntp4vc_patience_game_inv ntp4vc_patience_game_initial_state /\
    (!s:ntp4vc_patience_game_state.
       ntp4vc_patience_game_final_state_obligation input s
       ==>
       if ntp4vc_patience_game_num_stacks s = (&0:int) then
         ntp4vc_patience_game_maximal_subsequence s input
       else
         ntp4vc_patience_game_nonempty_branch s input)`;;
