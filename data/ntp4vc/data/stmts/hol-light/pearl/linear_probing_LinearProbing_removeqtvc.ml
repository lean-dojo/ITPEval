(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_removeqtvc: the verification condition
  for removing a key from a linear-probing hash table, including cyclic
  probing, creation of a vacant slot, and preservation of the table validity
  invariant and abstract membership view. This file contains no proof.
*)

let lp_remove_int_index = new_definition
 `lp_remove_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let lp_remove_nth = new_definition
 `lp_remove_nth (xs:A list) (i:int) =
    if lp_remove_int_index i < LENGTH xs
    then EL (lp_remove_int_index i) xs
    else ARB`;;

let lp_remove_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       lp_remove_update_nat [] n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       lp_remove_update_nat (CONS h t) n x =
       if n = 0
       then CONS x t
       else CONS h (lp_remove_update_nat t (PRE n) x))`;;

let lp_remove_update_list = new_definition
 `lp_remove_update_list (xs:A list) (i:int) (x:A) =
    lp_remove_update_nat xs (lp_remove_int_index i) x`;;

let lp_remove_update_function = new_definition
 `lp_remove_update_function (f:A->B) (x:A) (y:B) =
    \z. if z = x then y else f z`;;

let lp_remove_bucket = new_definition
 `lp_remove_bucket (hash:A->int) (k:A) (n:int) = hash k rem n`;;

let lp_remove_between = new_definition
 `lp_remove_between (l:int) (j:int) (r:int) <=>
    (l <= j /\ j < r) \/
    (r < l /\ l <= j) \/
    (j < r /\ r < l)`;;

let lp_remove_next = new_definition
 `lp_remove_next (n:int) (i:int) =
    let i1 = i + (&1:int) in
    if i1 = n then (&0:int) else i1`;;

let lp_remove_numof_loop =
  new_recursive_definition num_RECURSION
   `(!p:int->bool.
     !i:int.
       lp_remove_numof_loop p i 0 = (&0:int)) /\
    (!p:int->bool.
     !i:int.
     !n:num.
       lp_remove_numof_loop p i (SUC n) =
       (if p i then (&1:int) else (&0:int)) +
       lp_remove_numof_loop p (i + (&1:int)) n)`;;

let lp_remove_numof = new_definition
 `lp_remove_numof
    (keym:A->B) (dummy:A) (xs:A list) (l:int) (u:int) =
    if u <= l then (&0:int)
    else
      lp_remove_numof_loop
        (\i. keym (lp_remove_nth xs i) = keym dummy)
        l (num_of_int (u - l))`;;

let lp_remove_valid = new_definition
 `lp_remove_valid
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
       let x = lp_remove_nth entries i in
         ~(keym x = keym dummy)
         ==> present (keym x) /\ location (keym x) = i) /\
    (let n = (&(LENGTH entries):int) in
       !x:A.
         present (keym x)
         ==>
         let i = location (keym x) in
           ((&0:int) <= i /\ i < n) /\
           keym (lp_remove_nth entries i) = keym x /\
           (!j:int.
              (&0:int) <= j /\ j < n
              ==>
              lp_remove_between (lp_remove_bucket hash x n) j i
              ==>
              ~(keym (lp_remove_nth entries j) = keym x) /\
              ~(keym (lp_remove_nth entries j) = keym dummy)))`;;

let lp_remove_state_invariant = new_definition
 `lp_remove_state_invariant
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
      lp_remove_numof keym dummy entries
        (&0:int) (&(LENGTH entries):int) =
      (&(LENGTH entries):int) /\
    lp_remove_valid keym dummy hash entries present location`;;

let lp_remove_completion_condition = new_definition
 `lp_remove_completion_condition
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (size:C->int)
    (data:C->A list)
    (view:C->B->bool)
    (loc:C->B->int)
    (x:A)
    (h:C)
    (j:int)
    (updated:A list) <=>
    !f0:int.
      ((&0:int) <= f0 /\ f0 < (&(LENGTH updated):int)) /\
      ~(f0 = j) /\
      keym (lp_remove_nth updated f0) = keym dummy /\
      (!k:int.
         (&0:int) <= k /\ k < (&(LENGTH updated):int)
         ==>
         lp_remove_between j k f0
         ==>
         ~(k = j)
         ==>
         ~(keym (lp_remove_nth updated k) = keym dummy))
      ==>
      ((&0:int) <= f0 /\ f0 < (&(LENGTH updated):int)) /\
      ((&0:int) <= j /\ j < (&(LENGTH updated):int)) /\
      ((&0:int) <= j /\ j < (&(LENGTH updated):int)) /\
      ~(j = f0) /\
      keym (lp_remove_nth updated j) = keym dummy /\
      keym (lp_remove_nth updated f0) = keym dummy /\
      lp_remove_between j j f0 /\
      (!k:int.
         (&0:int) <= k /\ k < (&(LENGTH updated):int)
         ==>
         lp_remove_between j k f0
         ==>
         ~(k = j)
         ==>
         ~(keym (lp_remove_nth updated k) = keym dummy)) /\
      ~(lp_remove_update_function
          (view h) (keym x) F (keym dummy)) /\
      (!k:int.
         (&0:int) <= k /\ k < (&(LENGTH updated):int)
         ==>
         let x1 = lp_remove_nth updated k in
           ~(keym x1 = keym dummy)
           ==>
           lp_remove_update_function
             (view h) (keym x) F (keym x1) /\
           loc h (keym x1) = k) /\
      (let n = (&(LENGTH updated):int) in
         !x1:A.
           lp_remove_update_function
             (view h) (keym x) F (keym x1)
           ==>
           let k = loc h (keym x1) in
             ((&0:int) <= k /\ k < n) /\
             keym (lp_remove_nth updated k) = keym x1 /\
             (!l:int.
                (&0:int) <= l /\ l < n
                ==>
                lp_remove_between
                  (lp_remove_bucket hash x1 n) l k
                ==>
                ~(keym (lp_remove_nth updated l) = keym x1) /\
                (~(keym (lp_remove_nth updated l) = keym dummy) \/
                 l = j /\ lp_remove_between j j k))) /\
      (!l:B->int.
       !h_data:A list.
         LENGTH h_data = LENGTH updated
         ==>
         LENGTH h_data = LENGTH updated
         ==>
         lp_remove_numof
           keym dummy h_data
           (&0:int) (&(LENGTH h_data):int) =
         lp_remove_numof
           keym dummy updated
           (&0:int) (&(LENGTH h_data):int) /\
         lp_remove_valid
           keym dummy hash h_data
           (lp_remove_update_function (view h) (keym x) F)
           l
         ==>
         !h1:C.
           lp_remove_state_invariant
             keym dummy hash
             (size h - (&1:int))
             h_data
             (lp_remove_update_function (view h) (keym x) F)
             l /\
           (l = loc h1 /\
            lp_remove_update_function
              (view h) (keym x) F = view h1 /\
            h_data = data h1 /\
            size h - (&1:int) = size h1
            ==>
            view h1 =
              lp_remove_update_function (view h) (keym x) F))`;;

let lp_remove_after_clear_condition = new_definition
 `lp_remove_after_clear_condition
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (size:C->int)
    (data:C->A list)
    (view:C->B->bool)
    (loc:C->B->int)
    (x:A)
    (h:C)
    (j:int)
    (updated:A list)
    (o7:int) <=>
    ((&0:int) <= j /\ j < (&(LENGTH updated):int)) /\
    ((&0:int) <= o7 /\ o7 < (&(LENGTH updated):int)) /\
    ~(o7 = j) /\
    (if j <= o7 then
       (&1:int) <=
         lp_remove_numof
           keym dummy updated o7 (&(LENGTH updated):int) +
         lp_remove_numof keym dummy updated (&0:int) j
     else
       (&1:int) <= lp_remove_numof keym dummy updated o7 j) /\
    (!k:int.
       (&0:int) <= k /\ k < (&(LENGTH updated):int)
       ==>
       lp_remove_between j k o7
       ==>
       ~(k = j)
       ==>
       ~(keym (lp_remove_nth updated k) = keym dummy)) /\
    lp_remove_completion_condition
      keym dummy hash size data view loc x h j updated`;;

let lp_remove_clear_condition = new_definition
 `lp_remove_clear_condition
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (size:C->int)
    (data:C->A list)
    (view:C->B->bool)
    (loc:C->B->int)
    (x:A)
    (h:C)
    (j:int)
    (o6:A list) <=>
    ((&0:int) <= j /\ j < (&(LENGTH o6):int)) /\
    (LENGTH (lp_remove_update_list o6 j dummy) = LENGTH o6
     ==>
     LENGTH (lp_remove_update_list o6 j dummy) = LENGTH (data h)
     ==>
     (!q:int.
        (&0:int) <= q /\ q < (&(LENGTH o6):int)
        ==>
        lp_remove_nth (lp_remove_update_list o6 j dummy) q =
          lp_remove_update_function (lp_remove_nth o6) j dummy q)
     ==>
     let updated = lp_remove_update_list o6 j dummy in
     let o7 = lp_remove_next (&(LENGTH (data h)):int) j in
       lp_remove_after_clear_condition
         keym dummy hash size data view loc x h j updated o7)`;;

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
        (&0:int) <= lp_remove_bucket hash k n /\
        lp_remove_bucket hash k n < n) /\
     (!self:C.
        lp_remove_state_invariant
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
    let o1 = data h in
      (~(keym x = keym dummy) /\
       (let n = (&(LENGTH o1):int) in
          (&0:int) < n /\
          (&0:int) <
            lp_remove_numof keym dummy o1 (&0:int) n) /\
      (!j:int.
         ((&0:int) <= j /\ j < (&(LENGTH o1):int)) /\
         (keym (lp_remove_nth o1 j) = keym dummy \/
          keym (lp_remove_nth o1 j) = keym x) /\
         (!j1:int.
            (&0:int) <= j1 /\ j1 < (&(LENGTH o1):int)
            ==>
            lp_remove_between
              (lp_remove_bucket hash x (&(LENGTH o1):int)) j1 j
            ==>
            ~(keym (lp_remove_nth o1 j1) = keym x) /\
            ~(keym (lp_remove_nth o1 j1) = keym dummy))
         ==>
         let o2 = dummy in
         let o3 = data h in
           ((&0:int) <= j /\ j < (&(LENGTH o3):int)) /\
           (let o4 = lp_remove_nth o3 j in
              (~(keym o4 = keym o2) <=>
               ~(keym o4 = keym o2))
              ==>
              if ~(keym o4 = keym o2) then
                let o5 = dummy in
                let o6 = data h in
                  lp_remove_clear_condition
                    keym o5 hash size data view loc x h j o6
              else
                view h =
                  lp_remove_update_function
                    (view h) (keym x) F)))`;;
