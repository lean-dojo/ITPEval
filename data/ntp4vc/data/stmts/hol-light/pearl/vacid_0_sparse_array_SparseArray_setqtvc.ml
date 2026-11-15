(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_sparse_array_SparseArray_setqtvc: the sparse-array set
  verification condition, preserving the representation invariant while
  updating one value and, when needed, inserting its sparse index. This file
  contains no proof.
*)

let sparse_array_set_int_index = new_definition
 `sparse_array_set_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let sparse_array_set_nth = new_definition
 `sparse_array_set_nth (default:A) (xs:A list) (i:int) =
    if i < (&0:int) then default
    else if sparse_array_set_int_index i < LENGTH xs
    then EL (sparse_array_set_int_index i) xs
    else default`;;

let sparse_array_set_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !x:A.
       sparse_array_set_update_nat [] n x = []) /\
    (!h:A.
     !t:A list.
     !n:num.
     !x:A.
       sparse_array_set_update_nat (CONS h t) n x =
       if n = 0
       then CONS x t
       else CONS h (sparse_array_set_update_nat t (PRE n) x))`;;

let sparse_array_set_update = new_definition
 `sparse_array_set_update (xs:A list) (i:int) (x:A) =
    sparse_array_set_update_nat xs (sparse_array_set_int_index i) x`;;

let sparse_array_set_update_function = new_definition
 `sparse_array_set_update_function (f:int->A) (i:int) (x:A) =
    \j. if j = i then x else f j`;;

let sparse_array_set_valid = new_definition
 `sparse_array_set_valid
    (vals:A list)
    (idx:int list)
    (bak:int list)
    (c:int) <=>
    (&0:int) <= c /\
    c <= (&(LENGTH vals):int) /\
    (&(LENGTH vals):int) <= (&1000:int) /\
    LENGTH vals = LENGTH idx /\
    LENGTH idx = LENGTH bak /\
    (!i:int.
       (&0:int) <= i /\ i < c
       ==>
       ((&0:int) <= sparse_array_set_nth (&0:int) bak i /\
        sparse_array_set_nth (&0:int) bak i <
          (&(LENGTH vals):int)) /\
       sparse_array_set_nth
         (&0:int) idx
         (sparse_array_set_nth (&0:int) bak i) =
       i)`;;

let sparse_array_set_context = new_definition
 `sparse_array_set_context
    (values:S->A list)
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (def1:S->A) <=>
    (!self:S.
       sparse_array_set_valid
         (values self) (index self) (back self) (card self)) /\
    (!a b:S.
       values a = values b /\
       index a = index b /\
       back a = back b /\
       card a = card b /\
       def1 a = def1 b
       ==> a = b)`;;

let sparse_array_set_is_elt = new_definition
 `sparse_array_set_is_elt
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (a:S)
    (i:int) <=>
    ((&0:int) <= sparse_array_set_nth (&0:int) (index a) i /\
     sparse_array_set_nth (&0:int) (index a) i < card a) /\
    sparse_array_set_nth
      (&0:int) (back a)
      (sparse_array_set_nth (&0:int) (index a) i) =
    i`;;

let sparse_array_set_value = new_definition
 `sparse_array_set_value
    (inhabitant:A)
    (values:S->A list)
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (def1:S->A)
    (a:S)
    (i:int) =
    if sparse_array_set_is_elt index back card a i
    then sparse_array_set_nth inhabitant (values a) i
    else def1 a`;;

let sparse_array_set_length = new_definition
 `sparse_array_set_length (values:S->A list) (a:S) =
    (&(LENGTH (values a)):int)`;;

let sparse_array_set_post = new_definition
 `sparse_array_set_post
    (inhabitant:A)
    (values:S->A list)
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (def1:S->A)
    (old:S)
    (newer:S)
    (i:int)
    (v:A) <=>
    sparse_array_set_value
      inhabitant values index back card def1 newer i =
    v /\
    (!j:int.
       ~(j = i)
       ==>
       sparse_array_set_value
         inhabitant values index back card def1 newer j =
       sparse_array_set_value
         inhabitant values index back card def1 old j)`;;

let statement =
 `!inhabitant:A.
  !values:S->A list.
  !index:S->int list.
  !back:S->int list.
  !card:S->int.
  !def1:S->A.
    sparse_array_set_context values index back card def1
    ==>
    !i:int.
    !a:S.
    !v:A.
      (&0:int) <= i
      ==>
      i < sparse_array_set_length values a
      ==>
      let o1 = values a in
      ((&0:int) <= i /\ i < (&(LENGTH o1):int)) /\
      (!a1:S.
         LENGTH (sparse_array_set_update o1 i v) = LENGTH o1
         ==>
         LENGTH (sparse_array_set_update o1 i v) =
           LENGTH (values a)
         ==>
         (\k:int.
            sparse_array_set_nth
              inhabitant (sparse_array_set_update o1 i v) k) =
           sparse_array_set_update_function
             (\k:int. sparse_array_set_nth inhabitant o1 k) i v
         ==>
         sparse_array_set_valid
           (sparse_array_set_update o1 i v)
           (index a)
           (back a)
           (card a) /\
         (def1 a = def1 a1 /\
          card a = card a1 /\
          back a = back a1 /\
          index a = index a1 /\
          sparse_array_set_update o1 i v = values a1
          ==>
          ((&0:int) <= i /\
           i < sparse_array_set_length values a1) /\
          (if ~(sparse_array_set_is_elt index back card a1 i)
           then
             let o2 = card a1 in
             let o3 = index a1 in
             ((&0:int) <= i /\ i < (&(LENGTH o3):int)) /\
             (LENGTH (sparse_array_set_update o3 i o2) = LENGTH o3
              ==>
              LENGTH (sparse_array_set_update o3 i o2) =
                LENGTH (index a1)
              ==>
              (\k:int.
                 sparse_array_set_nth
                   (&0:int) (sparse_array_set_update o3 i o2) k) =
                sparse_array_set_update_function
                  (\k:int. sparse_array_set_nth (&0:int) o3 k) i o2
              ==>
              ((&0:int) <= card a1 /\
               card a1 < (&(LENGTH (back a1)):int)) /\
              (LENGTH
                 (sparse_array_set_update
                   (back a1) (card a1) i) =
                 LENGTH (back a1)
               ==>
               LENGTH
                 (sparse_array_set_update
                   (back a1) (card a1) i) =
                 LENGTH (back a1)
               ==>
               (\k:int.
                  sparse_array_set_nth
                    (&0:int)
                    (sparse_array_set_update
                      (back a1) (card a1) i)
                    k) =
                 sparse_array_set_update_function
                   (\k:int.
                      sparse_array_set_nth (&0:int) (back a1) k)
                   (card a1) i
               ==>
               (!a2:S.
                  sparse_array_set_valid
                    (values a1)
                    (sparse_array_set_update o3 i o2)
                    (sparse_array_set_update
                      (back a1) (card a1) i)
                    (card a1 + (&1:int)) /\
                  (def1 a1 = def1 a2 /\
                   card a1 + (&1:int) = card a2 /\
                   sparse_array_set_update
                     (back a1) (card a1) i =
                     back a2 /\
                   sparse_array_set_update o3 i o2 = index a2 /\
                   values a1 = values a2
                   ==>
                   sparse_array_set_post
                     inhabitant values index back card def1
                     a a2 i v))))
           else
             sparse_array_set_post
               inhabitant values index back card def1 a a1 i v)))`;;
