(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Balance_insert_leavesqtvc: the verification condition for
  recursively inserting a rope's leaves into a balance queue while preserving
  rope invariants and appending the rope's modeled string. This file contains
  no proof.
*)

let ropes_insert_rope_INDUCT,ropes_insert_rope_RECURSION = define_type
  "ropes_insert_rope =
       RopesInsertEmp
     | RopesInsertStr S int int
     | RopesInsertApp ropes_insert_rope ropes_insert_rope int";;

let ropes_insert_length =
  new_recursive_definition ropes_insert_rope_RECURSION
   `(ropes_insert_length
       (RopesInsertEmp:S ropes_insert_rope) = (&0:int)) /\
    (!s:S. !ofs len:int.
       ropes_insert_length (RopesInsertStr s ofs len) = len) /\
    (!left right:S ropes_insert_rope. !len:int.
       ropes_insert_length (RopesInsertApp left right len) = len)`;;

let ropes_insert_inv =
  new_recursive_definition ropes_insert_rope_RECURSION
   `(!string_length:S->int.
       ropes_insert_inv string_length
         (RopesInsertEmp:S ropes_insert_rope) = T) /\
    (!string_length:S->int. !s:S. !ofs len:int.
       ropes_insert_inv string_length (RopesInsertStr s ofs len) =
       ((&0:int) < len /\
        ((&0:int) <= ofs /\ ofs < string_length s) /\
        ofs + len <= string_length s)) /\
    (!string_length:S->int.
     !left right:S ropes_insert_rope.
     !len:int.
       ropes_insert_inv string_length
         (RopesInsertApp left right len) =
       ((&0:int) < ropes_insert_length left /\
        ropes_insert_inv string_length left /\
        (&0:int) < ropes_insert_length right /\
        ropes_insert_inv string_length right /\
        len = ropes_insert_length left + ropes_insert_length right))`;;

let ropes_insert_string =
  new_recursive_definition ropes_insert_rope_RECURSION
   `(!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
       ropes_insert_string empty string_sub string_app
         (RopesInsertEmp:S ropes_insert_rope) = empty) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !s:S.
     !ofs len:int.
       ropes_insert_string empty string_sub string_app
         (RopesInsertStr s ofs len) =
       string_sub s ofs len) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !left right:S ropes_insert_rope.
     !len:int.
       ropes_insert_string empty string_sub string_app
         (RopesInsertApp left right len) =
       string_app
         (ropes_insert_string empty string_sub string_app left)
         (ropes_insert_string empty string_sub string_app right))`;;

let ropes_insert_string_equal = new_definition
 `ropes_insert_string_equal
    (string_length:S->int)
    (string_index:S->int->C)
    (left:S) (right:S) <=>
    string_length left = string_length right /\
    (!i:int.
       (&0:int) <= i /\ i < string_length left
       ==> string_index left i = string_index right i)`;;

let ropes_insert_int_index = new_definition
 `ropes_insert_int_index (index:int) =
    if index < (&0:int) then 0 else num_of_int index`;;

let ropes_insert_nth = new_definition
 `ropes_insert_nth
    (default:S ropes_insert_rope)
    (queue:(S ropes_insert_rope) list)
    (index:int) =
    if ropes_insert_int_index index < LENGTH queue
    then EL (ropes_insert_int_index index) queue
    else default`;;

let ropes_insert_string_of_queue = new_definition
 `ropes_insert_string_of_queue
    (string_of_array:(S ropes_insert_rope) list->int->int->S)
    (queue:(S ropes_insert_rope) list) =
    string_of_array queue (&2:int) (&(LENGTH queue):int)`;;

let ropes_insert_immediate_child =
  new_recursive_definition ropes_insert_rope_RECURSION
   `(!child:S ropes_insert_rope.
       ropes_insert_immediate_child
         (RopesInsertEmp:S ropes_insert_rope) child = F) /\
    (!s:S. !ofs len:int. !child:S ropes_insert_rope.
       ropes_insert_immediate_child
         (RopesInsertStr s ofs len) child = F) /\
    (!left right:S ropes_insert_rope. !len:int.
     !child:S ropes_insert_rope.
       ropes_insert_immediate_child
         (RopesInsertApp left right len) child =
       (left = child \/ right = child))`;;

let ropes_insert_context = new_definition
 `ropes_insert_context
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S)
    (fib:int->int)
    (maximum:int)
    (string_of_array:(S ropes_insert_rope) list->int->int->S)
    (default:S ropes_insert_rope) <=>
    (!s:S. (&0:int) <= string_length s) /\
    string_length empty = (&0:int) /\
    (!left right:S.
       ropes_insert_string_equal string_length string_index left right
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
    (!queue:(S ropes_insert_rope) list. !lower:int.
       (&0:int) <= lower /\ lower <= (&(LENGTH queue):int)
       ==> ropes_insert_string_equal string_length string_index
             (string_of_array queue lower lower) empty) /\
    (!queue:(S ropes_insert_rope) list. !lower upper:int.
       (&0:int) <= lower /\ lower < upper /\
       upper <= (&(LENGTH queue):int)
       ==> ropes_insert_string_equal string_length string_index
             (string_of_array queue lower upper)
             (string_app
               (string_of_array queue (lower + (&1:int)) upper)
               (ropes_insert_string empty string_sub string_app
                 (ropes_insert_nth default queue lower))))`;;

let ropes_insert_conclusion =
  new_recursive_definition ropes_insert_rope_RECURSION
   `(!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !fib:int->int.
     !maximum:int.
     !string_of_array:(S ropes_insert_rope) list->int->int->S.
     !default:S ropes_insert_rope.
     !queue:(S ropes_insert_rope) list.
       ropes_insert_conclusion
         string_length string_index empty string_app string_sub fib maximum
         string_of_array default queue
         (RopesInsertEmp:S ropes_insert_rope) =
       ((!j:int.
           (&2:int) <= j /\ j <= maximum
           ==> ropes_insert_inv string_length
                 (ropes_insert_nth default queue j)) /\
        ropes_insert_string_equal string_length string_index
          (ropes_insert_string_of_queue string_of_array queue)
          (string_app
            (ropes_insert_string_of_queue string_of_array queue)
            (ropes_insert_string
              empty string_sub string_app RopesInsertEmp)))) /\
    (!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !fib:int->int.
     !maximum:int.
     !string_of_array:(S ropes_insert_rope) list->int->int->S.
     !default:S ropes_insert_rope.
     !queue:(S ropes_insert_rope) list.
     !s:S.
     !ofs len:int.
       ropes_insert_conclusion
         string_length string_index empty string_app string_sub fib maximum
         string_of_array default queue (RopesInsertStr s ofs len) =
       ((((&2:int) <= (&2:int) /\
          (&2:int) < (&(LENGTH queue):int) /\
          (&(LENGTH queue):int) = maximum + (&1:int)) /\
         ropes_insert_inv string_length (RopesInsertStr s ofs len) /\
         (!j:int.
            (&2:int) <= j /\ j <= maximum
            ==> ropes_insert_inv string_length
                  (ropes_insert_nth default queue j)) /\
         string_length
           (string_of_array queue (&2:int) (maximum + (&1:int))) +
           ropes_insert_length (RopesInsertStr s ofs len) <
           fib (maximum + (&1:int))) /\
        (!queue1:(S ropes_insert_rope) list.
           LENGTH queue1 = LENGTH queue
           ==>
           ((!j:int.
               (&2:int) <= j /\ j <= maximum
               ==> ropes_insert_inv string_length
                     (ropes_insert_nth default queue1 j)) /\
            (!j:int.
               (&2:int) <= j /\ j < (&2:int)
               ==> ropes_insert_nth default queue1 j =
                   ropes_insert_nth default queue j) /\
            ropes_insert_string_equal string_length string_index
              (string_of_array queue1 (&2:int) (maximum + (&1:int)))
              (string_app
                (string_of_array queue (&2:int) (maximum + (&1:int)))
                (ropes_insert_string
                  empty string_sub string_app
                  (RopesInsertStr s ofs len))))
           ==>
           ((!j:int.
               (&2:int) <= j /\ j <= maximum
               ==> ropes_insert_inv string_length
                     (ropes_insert_nth default queue1 j)) /\
            ropes_insert_string_equal string_length string_index
              (ropes_insert_string_of_queue string_of_array queue1)
              (string_app
                (ropes_insert_string_of_queue string_of_array queue)
                (ropes_insert_string
                  empty string_sub string_app
                  (RopesInsertStr s ofs len))))))) /\
    (!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !fib:int->int.
     !maximum:int.
     !string_of_array:(S ropes_insert_rope) list->int->int->S.
     !default:S ropes_insert_rope.
     !queue:(S ropes_insert_rope) list.
     !left right:S ropes_insert_rope.
     !len:int.
       ropes_insert_conclusion
         string_length string_index empty string_app string_sub fib maximum
         string_of_array default queue
         (RopesInsertApp left right len) =
       ((ropes_insert_immediate_child
           (RopesInsertApp left right len) left /\
         ((&2:int) < (&(LENGTH queue):int) /\
          (&(LENGTH queue):int) = maximum + (&1:int)) /\
         ropes_insert_inv string_length left /\
         (!j:int.
            (&2:int) <= j /\ j <= maximum
            ==> ropes_insert_inv string_length
                  (ropes_insert_nth default queue j)) /\
         string_length
           (ropes_insert_string_of_queue string_of_array queue) +
           ropes_insert_length left <
           fib (maximum + (&1:int))) /\
        (!queue1:(S ropes_insert_rope) list.
           LENGTH queue1 = LENGTH queue
           ==>
           ((!j:int.
               (&2:int) <= j /\ j <= maximum
               ==> ropes_insert_inv string_length
                     (ropes_insert_nth default queue1 j)) /\
            ropes_insert_string_equal string_length string_index
              (ropes_insert_string_of_queue string_of_array queue1)
              (string_app
                (ropes_insert_string_of_queue string_of_array queue)
                (ropes_insert_string empty string_sub string_app left)))
           ==>
           ((ropes_insert_immediate_child
               (RopesInsertApp left right len) right /\
             ((&2:int) < (&(LENGTH queue1):int) /\
              (&(LENGTH queue1):int) = maximum + (&1:int)) /\
             ropes_insert_inv string_length right /\
             (!j:int.
                (&2:int) <= j /\ j <= maximum
                ==> ropes_insert_inv string_length
                      (ropes_insert_nth default queue1 j)) /\
             string_length
               (ropes_insert_string_of_queue string_of_array queue1) +
               ropes_insert_length right <
               fib (maximum + (&1:int))) /\
            (!queue2:(S ropes_insert_rope) list.
               LENGTH queue2 = LENGTH queue1
               ==>
               ((!j:int.
                   (&2:int) <= j /\ j <= maximum
                   ==> ropes_insert_inv string_length
                         (ropes_insert_nth default queue2 j)) /\
                ropes_insert_string_equal string_length string_index
                  (ropes_insert_string_of_queue string_of_array queue2)
                  (string_app
                    (ropes_insert_string_of_queue string_of_array queue1)
                    (ropes_insert_string
                      empty string_sub string_app right)))
               ==>
               ((!j:int.
                   (&2:int) <= j /\ j <= maximum
                   ==> ropes_insert_inv string_length
                         (ropes_insert_nth default queue2 j)) /\
                ropes_insert_string_equal string_length string_index
                  (ropes_insert_string_of_queue string_of_array queue2)
                  (string_app
                    (ropes_insert_string_of_queue string_of_array queue)
                    (ropes_insert_string
                      empty string_sub string_app
                      (RopesInsertApp left right len)))))))))`;;

let statement =
 `!string_length:S->int.
  !string_index:S->int->C.
  !empty:S.
  !string_app:S->S->S.
  !string_sub:S->int->int->S.
  !fib:int->int.
  !maximum:int.
  !string_of_array:(S ropes_insert_rope) list->int->int->S.
  !default:S ropes_insert_rope.
    ropes_insert_context
      string_length string_index empty string_app string_sub fib maximum
      string_of_array default
    ==>
    !queue:(S ropes_insert_rope) list.
    !r:S ropes_insert_rope.
      (&2:int) < (&(LENGTH queue):int)
      ==>
      (&(LENGTH queue):int) = maximum + (&1:int)
      ==>
      ropes_insert_inv string_length r
      ==>
      (!j:int.
         (&2:int) <= j /\ j <= maximum
         ==> ropes_insert_inv string_length
               (ropes_insert_nth default queue j))
      ==>
      string_length
        (ropes_insert_string_of_queue string_of_array queue) +
        ropes_insert_length r <
        fib (maximum + (&1:int))
      ==>
      ropes_insert_conclusion
        string_length string_index empty string_app string_sub fib maximum
        string_of_array default queue r`;;
