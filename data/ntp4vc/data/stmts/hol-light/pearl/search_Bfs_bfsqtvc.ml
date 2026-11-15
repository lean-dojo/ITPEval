(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/search_Bfs_bfsqtvc: the breadth-first-search verification condition
  establishing and preserving frontier path-length, coverage, minimality, and
  successor-accumulation invariants, with the no-solution postcondition at
  termination. This file contains no proof.
*)

let ntp4vc_search_bfs_nth = new_definition
 `ntp4vc_search_bfs_nth (default:A) (xs:A list) (i:int) =
    if num_of_int i < LENGTH xs
    then EL (num_of_int i) xs
    else default`;;

let ntp4vc_search_bfs_path_RULES,
    ntp4vc_search_bfs_path_INDUCT,
    ntp4vc_search_bfs_path_CASES =
  new_inductive_definition
   `(!moves:A->A list.
     !s:A.
       ntp4vc_search_bfs_path moves s s (&0:int)) /\
    (!moves:A->A list.
     !s:A.
     !i:int.
       (&0:int) <= i /\
       i < (&(LENGTH (moves s)):int)
       ==>
       ntp4vc_search_bfs_path
         moves s (EL (num_of_int i) (moves s)) (&1:int)) /\
    (!moves:A->A list.
     !s t u:A.
     !n m:int.
       ntp4vc_search_bfs_path moves s t n /\
       ntp4vc_search_bfs_path moves t u m
       ==>
       ntp4vc_search_bfs_path moves s u (n + m))`;;

let ntp4vc_search_bfs_move = new_definition
 `ntp4vc_search_bfs_move
    (moves:A->A list) (s:A) (t:A) <=>
    ?i:int.
      ((&0:int) <= i /\ i < (&(LENGTH (moves s)):int)) /\
      t = EL (num_of_int i) (moves s)`;;

let ntp4vc_search_bfs_level_invariant = new_definition
 `ntp4vc_search_bfs_level_invariant
    (moves:A->A list)
    (start:A)
    (success:A->bool)
    (p:int)
    (cur:A list) <=>
    (&0:int) <= p /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH cur):int)
       ==>
       ntp4vc_search_bfs_path
         moves start (ntp4vc_search_bfs_nth start cur i) p) /\
    (!t:A.
       ntp4vc_search_bfs_path moves start t p
       ==> MEM t cur) /\
    (!t:A.
     !n:int.
       ntp4vc_search_bfs_path moves start t n
       ==> success t
       ==> p <= n)`;;

let ntp4vc_search_bfs_inner_invariant = new_definition
 `ntp4vc_search_bfs_inner_invariant
    (moves:A->A list)
    (success:A->bool)
    (default:A)
    (cur:A list)
    (i:int)
    (nxt:A list) <=>
    (!l:int.
       (&0:int) <= l /\ l < (&(LENGTH nxt):int)
       ==>
       ?j:int.
         ((&0:int) <= j /\ j < i) /\
         ntp4vc_search_bfs_move
           moves
           (ntp4vc_search_bfs_nth default cur j)
           (ntp4vc_search_bfs_nth default nxt l)) /\
    (!j k:int.
       (&0:int) <= j /\ j < i
       ==>
       (&0:int) <= k /\
       k < (&(LENGTH
                (moves (ntp4vc_search_bfs_nth default cur j))):int)
       ==>
       MEM
         (ntp4vc_search_bfs_nth
            default
            (moves (ntp4vc_search_bfs_nth default cur j))
            k)
         nxt) /\
    (!j:int.
       (&0:int) <= j /\ j < i
       ==>
       ~success (ntp4vc_search_bfs_nth default cur j))`;;

let ntp4vc_search_bfs_append_contract = new_definition
 `ntp4vc_search_bfs_append_contract
    (default:A)
    (o5:A list)
    (nxt:A list)
    (o6:A list) <=>
    (&(LENGTH o6):int) =
      (&(LENGTH o5):int) + (&(LENGTH nxt):int) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH o5):int)
       ==>
       ntp4vc_search_bfs_nth default o6 i =
       ntp4vc_search_bfs_nth default o5 i) /\
    (!i:int.
       (&(LENGTH o5):int) <= i /\ i < (&(LENGTH o6):int)
       ==>
       ntp4vc_search_bfs_nth default o6 i =
       ntp4vc_search_bfs_nth
         default nxt (i - (&(LENGTH o5):int)))`;;

let ntp4vc_search_bfs_process_step = new_definition
 `ntp4vc_search_bfs_process_step
    (moves:A->A list)
    (start:A)
    (success:A->bool)
    (p:int)
    (cur:A list)
    (i:int)
    (nxt:A list) <=>
    let s = ntp4vc_search_bfs_nth start cur i in
    if success s then
      ntp4vc_search_bfs_path moves start s p
    else
      let o5 = moves s in
      let o6 = APPEND o5 nxt in
      ntp4vc_search_bfs_append_contract start o5 nxt o6
      ==>
      ntp4vc_search_bfs_inner_invariant
        moves success start cur (i + (&1:int)) o6`;;

let ntp4vc_search_bfs_for_obligation = new_definition
 `ntp4vc_search_bfs_for_obligation
    (moves:A->A list)
    (start:A)
    (success:A->bool)
    (p:int)
    (cur:A list)
    (o4:int)
    (nxt:A list) <=>
    (!i:int.
       (((&0:int) <= i /\ i <= o4) /\
        ntp4vc_search_bfs_inner_invariant
          moves success start cur i nxt)
       ==>
       ntp4vc_search_bfs_process_step
         moves start success p cur i nxt) /\
    (ntp4vc_search_bfs_inner_invariant
       moves success start cur (o4 + (&1:int)) nxt
     ==>
     ntp4vc_search_bfs_level_invariant
       moves start success (p + (&1:int)) nxt)`;;

let ntp4vc_search_bfs_nonempty_obligation = new_definition
 `ntp4vc_search_bfs_nonempty_obligation
    (moves:A->A list)
    (start:A)
    (success:A->bool)
    (p:int)
    (cur:A list)
    (o4:int) <=>
    ((&0:int) <= o4 + (&1:int)
     ==>
     ntp4vc_search_bfs_inner_invariant
       moves success start cur (&0:int) ([]:A list) /\
     (!nxt:A list.
        ntp4vc_search_bfs_for_obligation
          moves start success p cur o4 nxt)) /\
    (o4 + (&1:int) < (&0:int)
     ==>
     ntp4vc_search_bfs_level_invariant
       moves start success (p + (&1:int)) ([]:A list))`;;

let ntp4vc_search_Bfs_bfsqtvc =
 `!moves:A->A list.
  !start:A.
  !success:A->bool.
    let o1 = ([]:A list) in
    let o2 = start in
    let o3 = CONS o2 o1 in
    (&(LENGTH o3):int) =
      (&1:int) + (&(LENGTH o1):int) /\
    ntp4vc_search_bfs_nth start o3 (&0:int) = o2 /\
    (!i:int.
       (&0:int) < i /\ i <= (&(LENGTH o1):int)
       ==>
       ntp4vc_search_bfs_nth start o3 i =
       ntp4vc_search_bfs_nth start o1 (i - (&1:int)))
    ==>
    ntp4vc_search_bfs_level_invariant
      moves start success (&0:int) o3 /\
    (!p:int.
     !cur:A list.
       ntp4vc_search_bfs_level_invariant
         moves start success p cur
       ==>
       if (&0:int) < (&(LENGTH cur):int) then
         let o4 = (&(LENGTH cur):int) - (&1:int) in
         ntp4vc_search_bfs_nonempty_obligation
           moves start success p cur o4
       else
         !t:A.
         !n:int.
           success t
           ==> ~ntp4vc_search_bfs_path moves start t n)`;;
