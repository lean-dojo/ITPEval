(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Balance_insertqtvc: the verification condition for inserting a
  rope into a balance queue, either storing the concatenation at the current
  index or recursively carrying it to the next index while preserving queue
  invariants and the modeled string. This file contains no proof.
*)

let ropes_balance_insert_rope_INDUCT,ropes_balance_insert_rope_RECURSION =
  define_type
   "ropes_balance_insert_rope =
        RopesBalanceInsertEmp
      | RopesBalanceInsertStr S int int
      | RopesBalanceInsertApp
          ropes_balance_insert_rope ropes_balance_insert_rope int";;

let ropes_balance_insert_length =
  new_recursive_definition ropes_balance_insert_rope_RECURSION
   `(ropes_balance_insert_length
       (RopesBalanceInsertEmp:S ropes_balance_insert_rope) = (&0:int)) /\
    (!s:S. !ofs len:int.
       ropes_balance_insert_length
         (RopesBalanceInsertStr s ofs len) = len) /\
    (!left right:S ropes_balance_insert_rope. !len:int.
       ropes_balance_insert_length
         (RopesBalanceInsertApp left right len) = len)`;;

let ropes_balance_insert_inv =
  new_recursive_definition ropes_balance_insert_rope_RECURSION
   `(!string_length:S->int.
       ropes_balance_insert_inv string_length
         (RopesBalanceInsertEmp:S ropes_balance_insert_rope) = T) /\
    (!string_length:S->int. !s:S. !ofs len:int.
       ropes_balance_insert_inv string_length
         (RopesBalanceInsertStr s ofs len) =
       ((&0:int) < len /\
        ((&0:int) <= ofs /\ ofs < string_length s) /\
        ofs + len <= string_length s)) /\
    (!string_length:S->int.
     !left right:S ropes_balance_insert_rope.
     !len:int.
       ropes_balance_insert_inv string_length
         (RopesBalanceInsertApp left right len) =
       ((&0:int) < ropes_balance_insert_length left /\
        ropes_balance_insert_inv string_length left /\
        (&0:int) < ropes_balance_insert_length right /\
        ropes_balance_insert_inv string_length right /\
        len =
          ropes_balance_insert_length left +
          ropes_balance_insert_length right))`;;

let ropes_balance_insert_string =
  new_recursive_definition ropes_balance_insert_rope_RECURSION
   `(!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
       ropes_balance_insert_string empty string_sub string_app
         (RopesBalanceInsertEmp:S ropes_balance_insert_rope) = empty) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !s:S.
     !ofs len:int.
       ropes_balance_insert_string empty string_sub string_app
         (RopesBalanceInsertStr s ofs len) =
       string_sub s ofs len) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !left right:S ropes_balance_insert_rope.
     !len:int.
       ropes_balance_insert_string empty string_sub string_app
         (RopesBalanceInsertApp left right len) =
       string_app
         (ropes_balance_insert_string empty string_sub string_app left)
         (ropes_balance_insert_string empty string_sub string_app right))`;;

let ropes_balance_insert_string_equal = new_definition
 `ropes_balance_insert_string_equal
    (string_length:S->int)
    (string_index:S->int->C)
    (left:S) (right:S) <=>
    string_length left = string_length right /\
    (!i:int.
       (&0:int) <= i /\ i < string_length left
       ==> string_index left i = string_index right i)`;;

let ropes_balance_insert_int_index = new_definition
 `ropes_balance_insert_int_index (index:int) =
    if index < (&0:int) then 0 else num_of_int index`;;

let ropes_balance_insert_nth = new_definition
 `ropes_balance_insert_nth
    (default:S ropes_balance_insert_rope)
    (queue:(S ropes_balance_insert_rope) list)
    (index:int) =
    if ropes_balance_insert_int_index index < LENGTH queue
    then EL (ropes_balance_insert_int_index index) queue
    else default`;;

let ropes_balance_insert_update_nat =
  new_recursive_definition list_RECURSION
   `(!n:num.
     !value:S ropes_balance_insert_rope.
       ropes_balance_insert_update_nat [] n value = []) /\
    (!head:S ropes_balance_insert_rope.
     !tail:(S ropes_balance_insert_rope) list.
     !n:num.
     !value:S ropes_balance_insert_rope.
       ropes_balance_insert_update_nat (CONS head tail) n value =
       if n = 0
       then CONS value tail
       else
         CONS head
           (ropes_balance_insert_update_nat tail (PRE n) value))`;;

let ropes_balance_insert_update = new_definition
 `ropes_balance_insert_update
    (queue:(S ropes_balance_insert_rope) list)
    (index:int)
    (value:S ropes_balance_insert_rope) =
    ropes_balance_insert_update_nat
      queue (ropes_balance_insert_int_index index) value`;;

let ropes_balance_insert_function_update = new_definition
 `ropes_balance_insert_function_update
    (f:A->B) (x:A) (y:B) =
    \z. if z = x then y else f z`;;

let ropes_balance_insert_context = new_definition
 `ropes_balance_insert_context
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S)
    (fib:int->int)
    (maximum:int)
    (string_of_array:(S ropes_balance_insert_rope) list->int->int->S)
    (default:S ropes_balance_insert_rope) <=>
    (!s:S. (&0:int) <= string_length s) /\
    string_length empty = (&0:int) /\
    (!left right:S.
       ropes_balance_insert_string_equal
         string_length string_index left right
       ==> left = right) /\
    (!left right:S.
       string_length (string_app left right) =
       string_length left + string_length right) /\
    (!left right:S. !i:int.
       (&0:int) <= i /\ i < string_length left
       ==> string_index (string_app left right) i =
           string_index left i) /\
    (!left right:S. !i:int.
       string_length left <= i /\
       i < string_length left + string_length right
       ==> string_index (string_app left right) i =
           string_index right (i - string_length left)) /\
    (!s:S. !ofs len:int.
       (&0:int) <= len /\
       (&0:int) <= ofs /\ ofs <= string_length s /\
       ofs + len <= string_length s
       ==> string_length (string_sub s ofs len) = len) /\
    (!s:S. !ofs len i:int.
       (&0:int) <= len /\
       (&0:int) <= ofs /\ ofs <= string_length s /\
       ofs + len <= string_length s /\
       (&0:int) <= i /\ i < len
       ==> string_index (string_sub s ofs len) i =
           string_index s (ofs + i)) /\
    (!n:int.
       (&0:int) <= n
       ==> fib n =
           if n = (&0:int) then (&0:int)
           else if n = (&1:int) then (&1:int)
           else fib (n - (&1:int)) + fib (n - (&2:int))) /\
    (&2:int) <= maximum /\
    (!queue:(S ropes_balance_insert_rope) list. !lower:int.
       (&0:int) <= lower /\ lower <= (&(LENGTH queue):int)
       ==> ropes_balance_insert_string_equal string_length string_index
             (string_of_array queue lower lower) empty) /\
    (!queue:(S ropes_balance_insert_rope) list. !lower upper:int.
       (&0:int) <= lower /\ lower < upper /\
       upper <= (&(LENGTH queue):int)
       ==> ropes_balance_insert_string_equal string_length string_index
             (string_of_array queue lower upper)
             (string_app
               (string_of_array queue (lower + (&1:int)) upper)
               (ropes_balance_insert_string
                 empty string_sub string_app
                 (ropes_balance_insert_nth default queue lower))))`;;

let statement =
 `!string_length:S->int.
  !string_index:S->int->C.
  !empty:S.
  !string_app:S->S->S.
  !string_sub:S->int->int->S.
  !fib:int->int.
  !maximum:int.
  !string_of_array:(S ropes_balance_insert_rope) list->int->int->S.
  !default:S ropes_balance_insert_rope.
    ropes_balance_insert_context
      string_length string_index empty string_app string_sub fib maximum
      string_of_array default
    ==>
    !i:int.
    !queue:(S ropes_balance_insert_rope) list.
    !r:S ropes_balance_insert_rope.
      (&2:int) <= i
      ==>
      i < (&(LENGTH queue):int)
      ==>
      (&(LENGTH queue):int) = maximum + (&1:int)
      ==>
      ropes_balance_insert_inv string_length r
      ==>
      (!j:int.
         (&2:int) <= j /\ j <= maximum
         ==> ropes_balance_insert_inv string_length
               (ropes_balance_insert_nth default queue j))
      ==>
      string_length
        (string_of_array queue i (maximum + (&1:int))) +
        ropes_balance_insert_length r <
        fib (maximum + (&1:int))
      ==>
      ((&0:int) <= i /\
       i < (&(LENGTH queue):int) /\
       (let o1 = ropes_balance_insert_nth default queue i in
          (ropes_balance_insert_inv string_length o1 /\
           ropes_balance_insert_inv string_length r) /\
          (!r':S ropes_balance_insert_rope.
             ropes_balance_insert_inv string_length r' /\
             ropes_balance_insert_string_equal string_length string_index
               (ropes_balance_insert_string
                 empty string_sub string_app r')
               (string_app
                 (ropes_balance_insert_string
                   empty string_sub string_app o1)
                 (ropes_balance_insert_string
                   empty string_sub string_app r))
             ==>
             let o2 = i + (&1:int) in
               (&0:int) <= o2 /\
               (if ropes_balance_insert_length r' < fib o2 then
                  (((&0:int) <= i /\ i < (&(LENGTH queue):int)) /\
                   (let updated =
                      ropes_balance_insert_update queue i r' in
                      LENGTH updated = LENGTH queue
                      ==>
                      ropes_balance_insert_nth default updated =
                        ropes_balance_insert_function_update
                          (ropes_balance_insert_nth default queue) i r'
                      ==>
                      (!j:int.
                         (&2:int) <= j /\ j <= maximum
                         ==> ropes_balance_insert_inv string_length
                               (ropes_balance_insert_nth
                                 default updated j)) /\
                      (!j:int.
                         (&2:int) <= j /\ j < i
                         ==> ropes_balance_insert_nth default updated j =
                             ropes_balance_insert_nth default queue j) /\
                      ropes_balance_insert_string_equal
                        string_length string_index
                        (string_of_array
                          updated i (maximum + (&1:int)))
                        (string_app
                          (string_of_array
                            queue i (maximum + (&1:int)))
                          (ropes_balance_insert_string
                            empty string_sub string_app r))))
                else
                  let o3 =
                    (RopesBalanceInsertEmp:
                      S ropes_balance_insert_rope) in
                  ((&0:int) <= i /\ i < (&(LENGTH queue):int)) /\
                  (let cleared =
                     ropes_balance_insert_update queue i o3 in
                     LENGTH cleared = LENGTH queue
                     ==>
                     ropes_balance_insert_nth default cleared =
                       ropes_balance_insert_function_update
                         (ropes_balance_insert_nth default queue) i o3
                     ==>
                     let o4 = i + (&1:int) in
                       ((((&0:int) <= maximum - i /\
                           maximum - o4 < maximum - i) /\
                          (((&2:int) <= o4 /\
                            o4 < (&(LENGTH cleared):int) /\
                            (&(LENGTH cleared):int) =
                              maximum + (&1:int)) /\
                           ropes_balance_insert_inv string_length r' /\
                           (!j:int.
                              (&2:int) <= j /\ j <= maximum
                              ==> ropes_balance_insert_inv string_length
                                    (ropes_balance_insert_nth
                                      default cleared j)) /\
                           string_length
                             (string_of_array
                               cleared o4 (maximum + (&1:int))) +
                             ropes_balance_insert_length r' <
                             fib (maximum + (&1:int)))) /\
                        (!queue1:(S ropes_balance_insert_rope) list.
                           LENGTH queue1 = LENGTH cleared
                           ==>
                           (!j:int.
                              (&2:int) <= j /\ j <= maximum
                              ==> ropes_balance_insert_inv string_length
                                    (ropes_balance_insert_nth
                                      default queue1 j)) /\
                           (!j:int.
                              (&2:int) <= j /\ j < o4
                              ==> ropes_balance_insert_nth
                                    default queue1 j =
                                  ropes_balance_insert_nth
                                    default cleared j) /\
                           ropes_balance_insert_string_equal
                             string_length string_index
                             (string_of_array
                               queue1 o4 (maximum + (&1:int)))
                             (string_app
                               (string_of_array
                                 cleared o4 (maximum + (&1:int)))
                               (ropes_balance_insert_string
                                 empty string_sub string_app r'))
                           ==>
                           (!j:int.
                              (&2:int) <= j /\ j <= maximum
                              ==> ropes_balance_insert_inv string_length
                                    (ropes_balance_insert_nth
                                      default queue1 j)) /\
                           (!j:int.
                              (&2:int) <= j /\ j < i
                              ==> ropes_balance_insert_nth
                                    default queue1 j =
                                  ropes_balance_insert_nth
                                    default queue j) /\
                           ropes_balance_insert_string_equal
                             string_length string_index
                             (string_of_array
                               queue1 i (maximum + (&1:int)))
                             (string_app
                               (string_of_array
                                 queue i (maximum + (&1:int)))
                               (ropes_balance_insert_string
                                 empty string_sub string_app r)))))))))`;;
