(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/vacid_0_sparse_array_SparseArray_getqtvc: the sparse-array get
  verification condition, preserving index bounds and agreement with the
  array's abstract value function. This file contains no proof.
*)

let sparse_array_get_int_index = new_definition
 `sparse_array_get_int_index (i:int) =
    if i < (&0:int) then 0 else num_of_int i`;;

let sparse_array_get_nth = new_definition
 `sparse_array_get_nth (default:A) (xs:A list) (i:int) =
    if sparse_array_get_int_index i < LENGTH xs
    then EL (sparse_array_get_int_index i) xs
    else default`;;

let sparse_array_get_invariant = new_definition
 `sparse_array_get_invariant
    (values:S->A list)
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (self:S) <=>
    (&0:int) <= card self /\
    card self <= (&(LENGTH (values self)):int) /\
    (&(LENGTH (values self)):int) <= (&1000:int) /\
    LENGTH (values self) = LENGTH (index self) /\
    LENGTH (index self) = LENGTH (back self) /\
    (!i:int.
       (&0:int) <= i /\ i < card self
       ==>
       ((&0:int) <=
          sparse_array_get_nth (&0:int) (back self) i /\
        sparse_array_get_nth (&0:int) (back self) i <
          (&(LENGTH (values self)):int)) /\
       sparse_array_get_nth
         (&0:int) (index self)
         (sparse_array_get_nth (&0:int) (back self) i) =
       i)`;;

let sparse_array_get_context = new_definition
 `sparse_array_get_context
    (values:S->A list)
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (def1:S->A) <=>
    (!self:S.
       sparse_array_get_invariant values index back card self) /\
    (!a b:S.
       values a = values b /\
       index a = index b /\
       back a = back b /\
       card a = card b /\
       def1 a = def1 b
       ==> a = b)`;;

let sparse_array_get_is_elt = new_definition
 `sparse_array_get_is_elt
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (a:S)
    (i:int) <=>
    ((&0:int) <= sparse_array_get_nth (&0:int) (index a) i /\
     sparse_array_get_nth (&0:int) (index a) i < card a) /\
    sparse_array_get_nth
      (&0:int) (back a)
      (sparse_array_get_nth (&0:int) (index a) i) =
    i`;;

let sparse_array_get_value = new_definition
 `sparse_array_get_value
    (inhabitant:A)
    (values:S->A list)
    (index:S->int list)
    (back:S->int list)
    (card:S->int)
    (def1:S->A)
    (a:S)
    (i:int) =
    if sparse_array_get_is_elt index back card a i
    then sparse_array_get_nth inhabitant (values a) i
    else def1 a`;;

let sparse_array_get_length = new_definition
 `sparse_array_get_length (values:S->A list) (a:S) =
    (&(LENGTH (values a)):int)`;;

let statement =
 `!inhabitant:A.
  !values:S->A list.
  !index:S->int list.
  !back:S->int list.
  !card:S->int.
  !def1:S->A.
    sparse_array_get_context values index back card def1
    ==>
    !i:int.
    !a:S.
      (&0:int) <= i
      ==>
      i < sparse_array_get_length values a
      ==>
      (&0:int) <= i /\
      i < sparse_array_get_length values a /\
      (sparse_array_get_is_elt index back card a i
       ==>
       (&0:int) <= i /\
       i < (&(LENGTH (values a)):int)) /\
      (!result:A.
         (if sparse_array_get_is_elt index back card a i
          then result =
               sparse_array_get_nth inhabitant (values a) i
          else result = def1 a)
         ==>
         result =
         sparse_array_get_value
           inhabitant values index back card def1 a i)`;;
