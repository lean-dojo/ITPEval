(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_memqtvc: the membership verification
  condition for a linear-probing hash table, relating a terminating probe
  position to the table's abstract membership view. This file contains no
  proof.
*)

let lp_mem_int_index = new_definition
 `lp_mem_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let lp_mem_nth = new_definition
 `lp_mem_nth (xs:A list) (i:int) =
    if lp_mem_int_index i < LENGTH xs
    then EL (lp_mem_int_index i) xs
    else ARB`;;

let lp_mem_bucket = new_definition
 `lp_mem_bucket (hash:A->int) (k:A) (n:int) = hash k rem n`;;

let lp_mem_between = new_definition
 `lp_mem_between (l:int) (j:int) (r:int) <=>
    (l <= j /\ j < r) \/
    (r < l /\ l <= j) \/
    (j < r /\ r < l)`;;

let lp_mem_numof_loop =
  new_recursive_definition num_RECURSION
   `(!p:int->bool.
     !i:int.
       lp_mem_numof_loop p i 0 = (&0:int)) /\
    (!p:int->bool.
     !i:int.
     !n:num.
       lp_mem_numof_loop p i (SUC n) =
       (if p i then (&1:int) else (&0:int)) +
       lp_mem_numof_loop p (i + (&1:int)) n)`;;

let lp_mem_numof = new_definition
 `lp_mem_numof
    (keym:A->B) (dummy:A) (xs:A list) (l:int) (u:int) =
    if u <= l then (&0:int)
    else
      lp_mem_numof_loop
        (\i. keym (lp_mem_nth xs i) = keym dummy)
        l (num_of_int (u - l))`;;

let lp_mem_valid = new_definition
 `lp_mem_valid
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (entries:A list)
    (present:B->bool)
    (location:B->int) <=>
    ~present (keym dummy) /\
    (!i:int.
       (&0:int) <= i /\ i < (&(LENGTH entries):int)
       ==>
       let x = lp_mem_nth entries i in
         ~(keym x = keym dummy)
         ==> present (keym x) /\ location (keym x) = i) /\
    (let n = (&(LENGTH entries):int) in
       !x:A.
         present (keym x)
         ==>
         let i = location (keym x) in
           ((&0:int) <= i /\ i < n) /\
           keym (lp_mem_nth entries i) = keym x /\
           (!j:int.
              (&0:int) <= j /\ j < n
              ==>
              lp_mem_between (lp_mem_bucket hash x n) j i
              ==>
              ~(keym (lp_mem_nth entries j) = keym x) /\
              ~(keym (lp_mem_nth entries j) = keym dummy)))`;;

let lp_mem_state_invariant = new_definition
 `lp_mem_state_invariant
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (state_size:int)
    (entries:A list)
    (present:B->bool)
    (location:B->int) <=>
    (&0:int) <= state_size /\
    state_size < (&(LENGTH entries):int) /\
    state_size +
      lp_mem_numof keym dummy entries
        (&0:int) (&(LENGTH entries):int) =
      (&(LENGTH entries):int) /\
    lp_mem_valid keym dummy hash entries present location`;;

let statement =
 `!keym:A->B.
  !hash:A->int.
  !dummy:A.
  !size:C->int.
  !data:C->A list.
  !view:C->B->bool.
  !loc:C->B->int.
  !x:A.
  !h:C.
    ((!k:A. (&0:int) <= hash k) /\
     (!u v:A. keym u = keym v ==> hash u = hash v) /\
     (!n:int.
      !k:A.
        (&0:int) < n
        ==>
        (&0:int) <= lp_mem_bucket hash k n /\
        lp_mem_bucket hash k n < n) /\
     (!self:C.
        lp_mem_state_invariant
          keym dummy hash
          (size self) (data self) (view self) (loc self)) /\
     (!a b:C.
        size a = size b /\
        data a = data b /\
        view a = view b /\
        loc a = loc b
        ==> a = b))
    ==>
    ~(keym x = keym dummy)
    ==>
    let o1 = dummy in
    let o2 = data h in
      (~(keym x = keym dummy) /\
       (let n = (&(LENGTH o2):int) in
          (&0:int) < n /\
          (&0:int) <
            lp_mem_numof keym dummy o2 (&0:int) n)) /\
      (!o3:int.
         ((&0:int) <= o3 /\ o3 < (&(LENGTH o2):int)) /\
         (keym (lp_mem_nth o2 o3) = keym dummy \/
          keym (lp_mem_nth o2 o3) = keym x) /\
         (!j:int.
            (&0:int) <= j /\ j < (&(LENGTH o2):int)
            ==>
            lp_mem_between
              (lp_mem_bucket hash x (&(LENGTH o2):int)) j o3
            ==>
            ~(keym (lp_mem_nth o2 j) = keym x) /\
            ~(keym (lp_mem_nth o2 j) = keym dummy))
         ==>
         let o4 = data h in
           ((&0:int) <= o3 /\ o3 < (&(LENGTH o4):int)) /\
           (let o5 = lp_mem_nth o4 o3 in
              (~(keym o5 = keym o1) <=>
               ~(keym o5 = keym o1))
              ==>
              (~(keym o5 = keym o1) <=>
               view h (keym x))))`;;
