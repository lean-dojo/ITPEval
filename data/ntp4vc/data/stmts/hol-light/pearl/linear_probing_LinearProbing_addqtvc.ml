(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/linear_probing_LinearProbing_addqtvc: the verification condition for
  adding a key to a linear-probing hash table, including resize, probing,
  representation-invariant, and abstract-view update obligations. This file
  contains no proof.
*)

let lp_add_int_index = new_definition
 `lp_add_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let lp_add_nth = new_definition
 `lp_add_nth (xs:A list) (i:int) =
    if lp_add_int_index i < LENGTH xs
    then EL (lp_add_int_index i) xs
    else ARB`;;

let lp_add_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       lp_add_update_nat [] n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       lp_add_update_nat (CONS h t) n x =
       if n = 0
       then CONS x t
       else CONS h (lp_add_update_nat t (PRE n) x))`;;

let lp_add_update_list = new_definition
 `lp_add_update_list (xs:A list) (i:int) (x:A) =
    lp_add_update_nat xs (lp_add_int_index i) x`;;

let lp_add_update_function = new_definition
 `lp_add_update_function (f:A->B) (x:A) (y:B) =
    \z. if z = x then y else f z`;;

let lp_add_array_function_equal = new_definition
 `lp_add_array_function_equal
    (xs:A list) (f:int->B) (g:int->B) <=>
    !i:int.
      (&0:int) <= i /\ i < (&(LENGTH xs):int)
      ==> f i = g i`;;

let lp_add_bucket = new_definition
 `lp_add_bucket (hash:A->int) (k:A) (n:int) = hash k rem n`;;

let lp_add_between = new_definition
 `lp_add_between (l:int) (j:int) (r:int) <=>
    (l <= j /\ j < r) \/
    (r < l /\ l <= j) \/
    (j < r /\ r < l)`;;

let lp_add_numof_loop =
  new_recursive_definition num_RECURSION
   `(!p:int->bool.
     !i:int.
       lp_add_numof_loop p i 0 = (&0:int)) /\
    (!p:int->bool.
     !i:int.
     !n:num.
       lp_add_numof_loop p i (SUC n) =
       (if p i then (&1:int) else (&0:int)) +
       lp_add_numof_loop p (i + (&1:int)) n)`;;

let lp_add_numof = new_definition
 `lp_add_numof
    (keym:A->B) (dummy:A) (xs:A list) (l:int) (u:int) =
    if u <= l then (&0:int)
    else
      lp_add_numof_loop
        (\i. keym (lp_add_nth xs i) = keym dummy)
        l (num_of_int (u - l))`;;

let lp_add_valid = new_definition
 `lp_add_valid
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
       let x = lp_add_nth entries i in
         ~(keym x = keym dummy)
         ==> present (keym x) /\ location (keym x) = i) /\
    (let n = (&(LENGTH entries):int) in
       !x:A.
         present (keym x)
         ==>
         let i = location (keym x) in
           ((&0:int) <= i /\ i < n) /\
           keym (lp_add_nth entries i) = keym x /\
           (!j:int.
              (&0:int) <= j /\ j < n
              ==>
              lp_add_between (lp_add_bucket hash x n) j i
              ==>
              ~(keym (lp_add_nth entries j) = keym x) /\
              ~(keym (lp_add_nth entries j) = keym dummy)))`;;

let lp_add_state_invariant = new_definition
 `lp_add_state_invariant
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
      lp_add_numof keym dummy entries
        (&0:int) (&(LENGTH entries):int) =
      (&(LENGTH entries):int) /\
    lp_add_valid keym dummy hash entries present location`;;

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
        (&0:int) <= lp_add_bucket hash k n /\
        lp_add_bucket hash k n < n) /\
     (!self:C.
        lp_add_state_invariant
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
    ((if (&(LENGTH (data h)):int) <=
          (&2:int) * (size h + (&1:int))
      then
        !h1:C.
          view h = view h1 /\ size h = size h1
          ==>
          (&(LENGTH (data h1)):int) =
            (&2:int) * (&(LENGTH (data h)):int)
          ==>
          size h1 + (&1:int) < (&(LENGTH (data h1)):int)
      else
        size h + (&1:int) < (&(LENGTH (data h)):int)) /\
     (!h1:C.
        view h = view h1 /\ size h = size h1
        ==>
        size h1 + (&1:int) < (&(LENGTH (data h1)):int)
        ==>
        let o1 = data h1 in
          (~(keym x = keym dummy) /\
           (let n = (&(LENGTH o1):int) in
              (&0:int) < n /\
              (&0:int) <
                lp_add_numof keym dummy o1 (&0:int) n)) /\
          (!i:int.
             ((&0:int) <= i /\ i < (&(LENGTH o1):int)) /\
             (keym (lp_add_nth o1 i) = keym dummy \/
              keym (lp_add_nth o1 i) = keym x) /\
             (!j:int.
                (&0:int) <= j /\ j < (&(LENGTH o1):int)
                ==>
                lp_add_between
                  (lp_add_bucket hash x (&(LENGTH o1):int)) j i
                ==>
                ~(keym (lp_add_nth o1 j) = keym x) /\
                ~(keym (lp_add_nth o1 j) = keym dummy))
             ==>
             let o2 = dummy in
             let o3 = data h1 in
               ((&0:int) <= i /\ i < (&(LENGTH o3):int)) /\
               (let o4 = lp_add_nth o3 i in
                  (keym o4 = keym o2 <=> keym o4 = keym o2)
                  ==>
                  if keym o4 = keym o2 then
                    ((&0:int) <= i /\
                     i < (&(LENGTH (data h1)):int)) /\
                    (LENGTH (lp_add_update_list (data h1) i x) =
                       LENGTH (data h1)
                     ==>
                     LENGTH (lp_add_update_list (data h1) i x) =
                       LENGTH (data h1)
                     ==>
                     lp_add_array_function_equal
                       (lp_add_update_list (data h1) i x)
                       (lp_add_nth
                         (lp_add_update_list (data h1) i x))
                       (lp_add_update_function
                         (lp_add_nth (data h1)) i x)
                     ==>
                     (!h2:C.
                        lp_add_state_invariant
                          keym dummy hash
                          (size h1 + (&1:int))
                          (lp_add_update_list (data h1) i x)
                          (lp_add_update_function
                            (view h1) (keym x) T)
                          (lp_add_update_function
                            (loc h1) (keym x) i) /\
                        (lp_add_update_function
                           (loc h1) (keym x) i = loc h2 /\
                         lp_add_update_function
                           (view h1) (keym x) T = view h2 /\
                         lp_add_update_list (data h1) i x = data h2 /\
                         size h1 + (&1:int) = size h2
                         ==>
                         view h2 =
                           lp_add_update_function
                             (view h) (keym x) T)))
                  else
                    !h2:C.
                      lp_add_state_invariant
                        keym dummy hash
                        (size h1)
                        (data h1)
                        (lp_add_update_function
                          (view h1) (keym x) T)
                        (lp_add_update_function
                          (loc h1) (keym x) i) /\
                      (lp_add_update_function
                         (loc h1) (keym x) i = loc h2 /\
                       lp_add_update_function
                         (view h1) (keym x) T = view h2 /\
                       data h1 = data h2 /\
                       size h1 = size h2
                       ==>
                       view h2 =
                         lp_add_update_function
                           (view h) (keym x) T)))))`;;
