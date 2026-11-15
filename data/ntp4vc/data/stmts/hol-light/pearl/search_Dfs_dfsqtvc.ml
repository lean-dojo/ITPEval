(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/search_Dfs_dfsqtvc: the depth-first-search verification condition for
  bounded successful paths, recursive child outcomes, and loop invariants over
  already searched successors. This file contains no proof.
*)

let ntp4vc_search_dfs_nth = new_definition
 `ntp4vc_search_dfs_nth (default:A) (xs:A list) (i:int) =
    if (&0:int) <= i /\ num_of_int i < LENGTH xs
    then EL (num_of_int i) xs
    else default`;;

let ntp4vc_search_dfs_path_RULES,
    ntp4vc_search_dfs_path_INDUCT,
    ntp4vc_search_dfs_path_CASES =
  new_inductive_definition
   `(!moves:A->A list.
     !s:A.
       ntp4vc_search_dfs_path moves s s (&0:int)) /\
    (!moves:A->A list.
     !s:A.
     !i:int.
       (&0:int) <= i /\
       i < (&(LENGTH (moves s)):int)
       ==>
       ntp4vc_search_dfs_path
         moves s (EL (num_of_int i) (moves s)) (&1:int)) /\
    (!moves:A->A list.
     !s t u:A.
     !n m:int.
       ntp4vc_search_dfs_path moves s t n /\
       ntp4vc_search_dfs_path moves t u m
       ==>
       ntp4vc_search_dfs_path moves s u (n + m))`;;

let ntp4vc_search_dfs_no_solution = new_definition
 `ntp4vc_search_dfs_no_solution
    (moves:A->A list)
    (success:A->bool)
    (s:A)
    (bound:int) <=>
    !t:A.
    !n:int.
      (&0:int) <= n /\ n <= bound
      ==>
      success t
      ==>
      ~ntp4vc_search_dfs_path moves s t n`;;

let ntp4vc_search_dfs_children_excluded = new_definition
 `ntp4vc_search_dfs_children_excluded
    (default:A)
    (moves:A->A list)
    (success:A->bool)
    (mv:A list)
    (upper:int)
    (bound:int) <=>
    !j:int.
    !t:A.
    !n:int.
      (&0:int) <= j /\ j < upper
      ==>
      ntp4vc_search_dfs_path
        moves (ntp4vc_search_dfs_nth default mv j) t n
      ==>
      success t
      ==>
      ~((&0:int) <= n /\ n < bound)`;;

let ntp4vc_search_dfs_outcome_contract = new_definition
 `ntp4vc_search_dfs_outcome_contract
    (moves:A->A list)
    (success:A->bool)
    (s:A)
    (bound:int)
    (outcome:(A#int)option) <=>
    if outcome = NONE then
      ntp4vc_search_dfs_no_solution moves success s bound
    else
      let result = @r:A#int. outcome = SOME r in
      ntp4vc_search_dfs_path moves s (FST result) (SND result) /\
      success (FST result) /\
      (&0:int) <= SND result /\
      SND result <= bound`;;

let ntp4vc_search_dfs_lifted_outcome = new_definition
 `ntp4vc_search_dfs_lifted_outcome
    (default:A)
    (moves:A->A list)
    (success:A->bool)
    (s:A)
    (mv:A list)
    (i:int)
    (bound:int)
    (outcome:(A#int)option) <=>
    if outcome = NONE then
      ntp4vc_search_dfs_children_excluded
        default moves success mv (i + (&1:int)) bound
    else
      let result = @r:A#int. outcome = SOME r in
      let o5 = SND result + (&1:int) in
      ntp4vc_search_dfs_path moves s (FST result) o5 /\
      success (FST result) /\
      (&0:int) <= o5 /\
      o5 <= bound`;;

let statement =
 `!moves:A->A list.
  !success:A->bool.
  !p:int.
  !m:int.
  !s:A.
    (&0:int) <= p
    ==>
    p <= m + (&1:int)
    ==>
    if m < p then
      ntp4vc_search_dfs_no_solution moves success s (m - p)
    else if success s then
      ntp4vc_search_dfs_path moves s s (&0:int) /\
      success s /\
      (&0:int) <= (&0:int) /\
      (&0:int) <= m - p
    else
      let mv = moves s in
      let o1 = (&(LENGTH mv):int) - (&1:int) in
      (((&0:int) <= o1 + (&1:int)
        ==>
        ntp4vc_search_dfs_children_excluded
          s moves success mv (&0:int) (m - p) /\
        (!i:int.
           (((&0:int) <= i /\ i <= o1) /\
            ntp4vc_search_dfs_children_excluded
              s moves success mv i (m - p))
           ==>
           let o2 = p + (&1:int) in
           let o3 = ntp4vc_search_dfs_nth s mv i in
           (((&0:int) <= m - p /\ m - o2 < m - p) /\
            (&0:int) <= o2 /\
            o2 <= m + (&1:int)) /\
           (!outcome:(A#int)option.
              ntp4vc_search_dfs_outcome_contract
                moves success o3 (m - o2) outcome
              ==>
              ntp4vc_search_dfs_lifted_outcome
                s moves success s mv i (m - p) outcome))) /\
       (ntp4vc_search_dfs_children_excluded
          s moves success mv (o1 + (&1:int)) (m - p)
        ==>
        ntp4vc_search_dfs_no_solution moves success s (m - p))) /\
      (o1 + (&1:int) < (&0:int)
       ==>
       ntp4vc_search_dfs_no_solution moves success s (m - p))`;;
