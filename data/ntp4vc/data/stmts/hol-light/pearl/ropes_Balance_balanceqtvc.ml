(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Balance_balanceqtvc: the rope-balancing verification condition
  for queue initialization, leaf insertion, and reconstruction of an
  invariant rope with the same modeled string. This file contains no proof.
*)

let ropes_balance_rope_INDUCT,ropes_balance_rope_RECURSION = define_type
  "ropes_balance_rope =
       RopesBalanceEmp
     | RopesBalanceStr S int int
     | RopesBalanceApp ropes_balance_rope ropes_balance_rope int";;

let ropes_balance_length =
  new_recursive_definition ropes_balance_rope_RECURSION
   `(ropes_balance_length
       (RopesBalanceEmp:S ropes_balance_rope) = (&0:int)) /\
    (!s:S. !ofs len:int.
       ropes_balance_length (RopesBalanceStr s ofs len) = len) /\
    (!left right:S ropes_balance_rope. !len:int.
       ropes_balance_length (RopesBalanceApp left right len) = len)`;;

let ropes_balance_inv =
  new_recursive_definition ropes_balance_rope_RECURSION
   `(!string_length:S->int.
       ropes_balance_inv string_length
         (RopesBalanceEmp:S ropes_balance_rope) = T) /\
    (!string_length:S->int. !s:S. !ofs len:int.
       ropes_balance_inv string_length (RopesBalanceStr s ofs len) =
       ((&0:int) < len /\
        ((&0:int) <= ofs /\ ofs < string_length s) /\
        ofs + len <= string_length s)) /\
    (!string_length:S->int.
     !left right:S ropes_balance_rope.
     !len:int.
       ropes_balance_inv string_length
         (RopesBalanceApp left right len) =
       ((&0:int) < ropes_balance_length left /\
        ropes_balance_inv string_length left /\
        (&0:int) < ropes_balance_length right /\
        ropes_balance_inv string_length right /\
        len = ropes_balance_length left + ropes_balance_length right))`;;

let ropes_balance_string =
  new_recursive_definition ropes_balance_rope_RECURSION
   `(!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
       ropes_balance_string empty string_sub string_app
         (RopesBalanceEmp:S ropes_balance_rope) = empty) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !s:S.
     !ofs len:int.
       ropes_balance_string empty string_sub string_app
         (RopesBalanceStr s ofs len) =
       string_sub s ofs len) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !left right:S ropes_balance_rope.
     !len:int.
       ropes_balance_string empty string_sub string_app
         (RopesBalanceApp left right len) =
       string_app
         (ropes_balance_string empty string_sub string_app left)
         (ropes_balance_string empty string_sub string_app right))`;;

let ropes_balance_string_equal = new_definition
 `ropes_balance_string_equal
    (string_length:S->int)
    (string_index:S->int->C)
    (left:S) (right:S) <=>
    string_length left = string_length right /\
    (!i:int.
       (&0:int) <= i /\ i < string_length left
       ==> string_index left i = string_index right i)`;;

let ropes_balance_int_index = new_definition
 `ropes_balance_int_index (index:int) =
    if index < (&0:int) then 0 else num_of_int index`;;

let ropes_balance_nth = new_definition
 `ropes_balance_nth
    (default:S ropes_balance_rope)
    (queue:(S ropes_balance_rope) list)
    (index:int) =
    if ropes_balance_int_index index < LENGTH queue
    then EL (ropes_balance_int_index index) queue
    else default`;;

let ropes_balance_string_of_queue = new_definition
 `ropes_balance_string_of_queue
    (string_of_array:(S ropes_balance_rope) list->int->int->S)
    (queue:(S ropes_balance_rope) list) =
    string_of_array queue (&2:int) (&(LENGTH queue):int)`;;

let ropes_balance_context = new_definition
 `ropes_balance_context
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S)
    (fib:int->int)
    (maximum:int)
    (string_of_array:(S ropes_balance_rope) list->int->int->S)
    (default:S ropes_balance_rope) <=>
    (!s:S. (&0:int) <= string_length s) /\
    string_length empty = (&0:int) /\
    (!left right:S.
       ropes_balance_string_equal string_length string_index left right
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
    (!queue:(S ropes_balance_rope) list. !lower:int.
       (&0:int) <= lower /\ lower <= (&(LENGTH queue):int)
       ==> ropes_balance_string_equal string_length string_index
             (string_of_array queue lower lower) empty) /\
    (!queue:(S ropes_balance_rope) list. !lower upper:int.
       (&0:int) <= lower /\ lower < upper /\
       upper <= (&(LENGTH queue):int)
       ==> ropes_balance_string_equal string_length string_index
             (string_of_array queue lower upper)
             (string_app
               (string_of_array queue (lower + (&1:int)) upper)
               (ropes_balance_string empty string_sub string_app
                 (ropes_balance_nth default queue lower))))`;;

let statement =
 `!string_length:S->int.
  !string_index:S->int->C.
  !empty:S.
  !string_app:S->S->S.
  !string_sub:S->int->int->S.
  !fib:int->int.
  !maximum:int.
  !string_of_array:(S ropes_balance_rope) list->int->int->S.
  !default:S ropes_balance_rope.
    ropes_balance_context
      string_length string_index empty string_app string_sub fib maximum
      string_of_array default
    ==>
    !r:S ropes_balance_rope.
      ropes_balance_inv string_length r
      ==>
      ropes_balance_length r < fib (maximum + (&1:int))
      ==>
      let o1 = maximum + (&1:int) in
      (&0:int) <= o1 /\
      (!queue:(S ropes_balance_rope) list.
         ((!i:int.
             (&0:int) <= i /\ i < o1
             ==> ropes_balance_nth default queue i = RopesBalanceEmp) /\
          (&(LENGTH queue):int) = o1)
         ==>
         (((&2:int) < (&(LENGTH queue):int) /\
           (&(LENGTH queue):int) = maximum + (&1:int)) /\
          ropes_balance_inv string_length r /\
          (!j:int.
             (&2:int) <= j /\ j <= maximum
             ==> ropes_balance_inv string_length
                   (ropes_balance_nth default queue j)) /\
          string_length
            (ropes_balance_string_of_queue string_of_array queue) +
            ropes_balance_length r <
            fib (maximum + (&1:int))) /\
         (!queue1:(S ropes_balance_rope) list.
            LENGTH queue1 = LENGTH queue
            ==>
            (!j:int.
               (&2:int) <= j /\ j <= maximum
               ==> ropes_balance_inv string_length
                     (ropes_balance_nth default queue1 j))
            ==>
            ropes_balance_string_equal string_length string_index
              (ropes_balance_string_of_queue string_of_array queue1)
              (string_app
                (ropes_balance_string_of_queue string_of_array queue)
                (ropes_balance_string empty string_sub string_app r))
            ==>
            let o2 = maximum in
            (((&2:int) <= o2 + (&1:int)
              ==>
              (ropes_balance_inv string_length RopesBalanceEmp /\
               ropes_balance_string_equal string_length string_index
                 (ropes_balance_string
                   empty string_sub string_app RopesBalanceEmp)
                 (string_of_array queue1 (&2:int) (&2:int))) /\
              (!res:S ropes_balance_rope.
                 ((!i:int.
                     (((&2:int) <= i /\ i <= o2) /\
                      ropes_balance_inv string_length res /\
                      ropes_balance_string_equal
                        string_length string_index
                        (ropes_balance_string
                          empty string_sub string_app res)
                        (string_of_array queue1 (&2:int) i))
                     ==>
                     ((&0:int) <= i /\
                      i < (&(LENGTH queue1):int)) /\
                     (let o3 = ropes_balance_nth default queue1 i in
                      (ropes_balance_inv string_length o3 /\
                       ropes_balance_inv string_length res) /\
                      (!o4:S ropes_balance_rope.
                         ropes_balance_inv string_length o4 /\
                         ropes_balance_string_equal
                           string_length string_index
                           (ropes_balance_string
                             empty string_sub string_app o4)
                           (string_app
                             (ropes_balance_string
                               empty string_sub string_app o3)
                             (ropes_balance_string
                               empty string_sub string_app res))
                         ==>
                         ropes_balance_inv string_length o4 /\
                         ropes_balance_string_equal
                           string_length string_index
                           (ropes_balance_string
                             empty string_sub string_app o4)
                           (string_of_array
                             queue1 (&2:int) (i + (&1:int))))))) /\
                  (ropes_balance_inv string_length res /\
                   ropes_balance_string_equal
                     string_length string_index
                     (ropes_balance_string
                       empty string_sub string_app res)
                     (string_of_array
                       queue1 (&2:int) (o2 + (&1:int)))
                   ==>
                   ropes_balance_inv string_length res /\
                   ropes_balance_string_equal
                     string_length string_index
                     (ropes_balance_string
                       empty string_sub string_app res)
                     (ropes_balance_string
                       empty string_sub string_app r)))))) /\
             (o2 + (&1:int) < (&2:int)
              ==>
              let result =
                (RopesBalanceEmp:S ropes_balance_rope) in
              ropes_balance_inv string_length result /\
              ropes_balance_string_equal string_length string_index
                (ropes_balance_string
                  empty string_sub string_app result)
                (ropes_balance_string
                  empty string_sub string_app r)))`;;
