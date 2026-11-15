(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_resizeqtvc: the resize verification
  condition for a linear-probing hash table, covering initialization,
  reinsertion-loop preservation, table validity, and doubled capacity. This
  file contains no proof.
*)

let lp_resize_int_index = new_definition
 `lp_resize_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let lp_resize_nth = new_definition
 `lp_resize_nth (xs:A list) (i:int) =
    if (&0:int) <= i /\ lp_resize_int_index i < LENGTH xs
    then EL (lp_resize_int_index i) xs
    else ARB`;;

let lp_resize_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       lp_resize_update_nat [] n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       lp_resize_update_nat (CONS h t) n x =
       if n = 0
       then CONS x t
       else CONS h (lp_resize_update_nat t (PRE n) x))`;;

let lp_resize_update_list = new_definition
 `lp_resize_update_list (xs:A list) (i:int) (x:A) =
    if (&0:int) <= i /\ lp_resize_int_index i < LENGTH xs
    then lp_resize_update_nat xs (lp_resize_int_index i) x
    else xs`;;

let lp_resize_update_function = new_definition
 `lp_resize_update_function (f:A->B) (x:A) (y:B) =
    \z. if z = x then y else f z`;;

let lp_resize_array_function_equal = new_definition
 `lp_resize_array_function_equal
    (xs:A list) (f:int->B) (g:int->B) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH xs):int)
      ==> f i = g i`;;

let lp_resize_bucket = new_definition
 `lp_resize_bucket (hash:A->int) (k:A) (n:int) = hash k rem n`;;

let lp_resize_between = new_definition
 `lp_resize_between (l:int) (j:int) (r:int) <=>
    (l <= j /\ j < r) \/
    (r < l /\ l <= j) \/
    (j < r /\ r < l)`;;

let lp_resize_numof_loop =
  new_recursive_definition num_RECURSION
   `(!p:int->bool.
     !i:int.
       lp_resize_numof_loop p i 0 = (&0:int)) /\
    (!p:int->bool.
     !i:int.
     !n:num.
       lp_resize_numof_loop p i (SUC n) =
       (if p i then (&1:int) else (&0:int)) +
       lp_resize_numof_loop p (i + (&1:int)) n)`;;

let lp_resize_numof = new_definition
 `lp_resize_numof
    (keym:A->B) (dummy:A) (xs:A list) (l:int) (u:int) =
    if u <= l then (&0:int)
    else
      lp_resize_numof_loop
        (\i. keym (lp_resize_nth xs i) = keym dummy)
        l (num_of_int (u - l))`;;

let lp_resize_valid = new_definition
 `lp_resize_valid
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
       let x = lp_resize_nth entries i in
         ~(keym x = keym dummy)
         ==> present (keym x) /\ location (keym x) = i) /\
    (let n = (&(LENGTH entries):int) in
       !x:A.
         present (keym x)
         ==>
         let i = location (keym x) in
           ((&0:int) <= i /\ i < n) /\
           keym (lp_resize_nth entries i) = keym x /\
           (!j:int.
              (&0:int) <= j /\ j < n
              ==>
              lp_resize_between (lp_resize_bucket hash x n) j i
              ==>
              ~(keym (lp_resize_nth entries j) = keym x) /\
              ~(keym (lp_resize_nth entries j) = keym dummy)))`;;

let lp_resize_state_invariant = new_definition
 `lp_resize_state_invariant
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
      lp_resize_numof keym dummy entries
        (&0:int) (&(LENGTH entries):int) =
      (&(LENGTH entries):int) /\
    lp_resize_valid keym dummy hash entries present location`;;

let lp_resize_loop_invariant = new_definition
 `lp_resize_loop_invariant
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (data:C->A list)
    (view:C->B->bool)
    (loc:C->B->int)
    (h:C)
    (entries:A list)
    (location:B->int)
    (n2:int)
    (i:int) <=>
    lp_resize_numof keym dummy entries (&0:int) n2 =
      lp_resize_numof keym dummy (data h) (&0:int) i + n2 - i /\
    (!j:int.
       (&0:int) <= j /\ j < n2
       ==>
       ~(keym (lp_resize_nth entries j) = keym dummy)
       ==>
       view h (keym (lp_resize_nth entries j)) /\
       location (keym (lp_resize_nth entries j)) = j) /\
    (!x:A.
       view h (keym x)
       ==>
       if loc h (keym x) < i then
         let j2 = location (keym x) in
           ((&0:int) <= j2 /\ j2 < n2) /\
           keym (lp_resize_nth entries j2) = keym x /\
           (!k:int.
              (&0:int) <= k /\ k < n2
              ==>
              lp_resize_between (lp_resize_bucket hash x n2) k j2
              ==>
              ~(keym (lp_resize_nth entries k) = keym x) /\
              ~(keym (lp_resize_nth entries k) = keym dummy))
       else
         !j2:int.
           (&0:int) <= j2 /\ j2 < n2
           ==>
           ~(keym (lp_resize_nth entries j2) = keym x))`;;

let lp_resize_result_condition = new_definition
 `lp_resize_result_condition
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (size:C->int)
    (data:C->A list)
    (view:C->B->bool)
    (loc:C->B->int)
    (h:C)
    (entries:A list)
    (location:B->int) <=>
    !h1:C.
      (((&0:int) <= size h /\
        size h < (&(LENGTH entries):int)) /\
       (let n3 = (&(LENGTH entries):int) in
          size h +
            lp_resize_numof keym dummy entries (&0:int) n3 = n3) /\
       lp_resize_valid keym dummy hash entries (view h) location) /\
      (location = loc h1 /\
       view h = view h1 /\
       entries = data h1 /\
       size h = size h1
       ==>
       (&(LENGTH (data h1)):int) =
         (&2:int) * (&(LENGTH (data h)):int))`;;

let lp_resize_step_condition = new_definition
 `lp_resize_step_condition
    (keym:A->B)
    (dummy:A)
    (hash:A->int)
    (data:C->A list)
    (view:C->B->bool)
    (loc:C->B->int)
    (h:C)
    (entries:A list)
    (location:B->int)
    (n2:int)
    (i:int) <=>
    let source = data h in
      ((&0:int) <= i /\ i < (&(LENGTH source):int)) /\
      (let x = lp_resize_nth source i in
       let o4 = dummy in
         (~(keym x = keym o4) <=> ~(keym x = keym o4))
         ==>
         if ~(keym x = keym o4) then
           (~(keym x = keym dummy) /\
            (let n1 = (&(LENGTH entries):int) in
               (&0:int) < n1 /\
               (&0:int) <
                 lp_resize_numof
                   keym dummy entries (&0:int) n1)) /\
           (!j:int.
              ((&0:int) <= j /\ j < (&(LENGTH entries):int)) /\
              (keym (lp_resize_nth entries j) = keym dummy \/
               keym (lp_resize_nth entries j) = keym x) /\
              (!j1:int.
                 (&0:int) <= j1 /\
                 j1 < (&(LENGTH entries):int)
                 ==>
                 lp_resize_between
                   (lp_resize_bucket
                     hash x (&(LENGTH entries):int)) j1 j
                 ==>
                 ~(keym (lp_resize_nth entries j1) = keym x) /\
                 ~(keym (lp_resize_nth entries j1) = keym dummy))
              ==>
              ((&0:int) <= j /\ j < (&(LENGTH entries):int)) /\
              (LENGTH (lp_resize_update_list entries j x) =
                 LENGTH entries
               ==>
               lp_resize_array_function_equal
                 (lp_resize_update_list entries j x)
                 (lp_resize_nth (lp_resize_update_list entries j x))
                 (lp_resize_update_function
                   (lp_resize_nth entries) j x)
               ==>
               lp_resize_loop_invariant
                 keym dummy hash data view loc h
                 (lp_resize_update_list entries j x)
                 (lp_resize_update_function
                   location (keym x) j)
                 n2 (i + (&1:int))))
         else
           lp_resize_loop_invariant
             keym dummy hash data view loc h
             entries location n2 (i + (&1:int)))`;;

let statement =
 `!keym:A->B.
  !hash:A->int.
  !dummy:A.
  !size:C->int.
  !data:C->A list.
  !view:C->B->bool.
  !loc:C->B->int.
  !h:C.
    ((!k:A. (&0:int) <= hash k) /\
     (!x y:A. keym x = keym y ==> hash x = hash y) /\
     (!n:int.
      !k:A.
        (&0:int) < n
        ==>
        (&0:int) <= lp_resize_bucket hash k n /\
        lp_resize_bucket hash k n < n) /\
     (!self:C.
        lp_resize_state_invariant
          keym dummy hash
          (size self) (data self) (view self) (loc self)) /\
     (!a b:C.
        size a = size b /\
        data a = data b /\
        view a = view b /\
        loc a = loc b
        ==> a = b))
    ==>
    let n = (&(LENGTH (data h)):int) in
    let n2 = (&2:int) * n in
      (&0:int) <= n2 /\
      (!a:A list.
         (!i:int.
            (&0:int) <= i /\ i < n2
            ==> lp_resize_nth a i = dummy) /\
         (&(LENGTH a):int) = n2
         ==>
         let initial_location = \m:B. (&0:int) in
         let last = n - (&1:int) in
           (((&0:int) <= last + (&1:int)
             ==>
             lp_resize_loop_invariant
               keym dummy hash data view loc h
               a initial_location n2 (&0:int) /\
             (!location:B->int.
              !entries:A list.
                LENGTH entries = LENGTH a
                ==>
                ((!i:int.
                    ((&0:int) <= i /\ i <= last) /\
                    lp_resize_loop_invariant
                      keym dummy hash data view loc h
                      entries location n2 i
                    ==>
                    lp_resize_step_condition
                      keym dummy hash data view loc h
                      entries location n2 i) /\
                 (lp_resize_loop_invariant
                    keym dummy hash data view loc h
                    entries location n2 (last + (&1:int))
                  ==>
                  lp_resize_result_condition
                    keym dummy hash size data view loc h
                    entries location)))) /\
            (last + (&1:int) < (&0:int)
             ==>
             lp_resize_result_condition
               keym dummy hash size data view loc h
               a initial_location)))`;;
