(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Rope_subqtvc: the sub-rope verification condition, covering
  recursive branch bounds and preservation of the rope invariant and modeled
  substring. This file contains no proof.
*)

let ropes_sub_rope_INDUCT,ropes_sub_rope_RECURSION = define_type
  "ropes_sub_rope =
       RopesSubEmp
     | RopesSubStr S int int
     | RopesSubApp ropes_sub_rope ropes_sub_rope int";;

let ropes_sub_length =
  new_recursive_definition ropes_sub_rope_RECURSION
   `(ropes_sub_length (RopesSubEmp:S ropes_sub_rope) = (&0:int)) /\
    (!s:S. !ofs len:int.
       ropes_sub_length (RopesSubStr s ofs len) = len) /\
    (!left right:S ropes_sub_rope. !len:int.
       ropes_sub_length (RopesSubApp left right len) = len)`;;

let ropes_sub_inv =
  new_recursive_definition ropes_sub_rope_RECURSION
   `(!string_length:S->int.
       ropes_sub_inv string_length
         (RopesSubEmp:S ropes_sub_rope) = T) /\
    (!string_length:S->int. !s:S. !ofs len:int.
       ropes_sub_inv string_length (RopesSubStr s ofs len) =
       ((&0:int) < len /\
        ((&0:int) <= ofs /\ ofs < string_length s) /\
        ofs + len <= string_length s)) /\
    (!string_length:S->int.
     !left right:S ropes_sub_rope.
     !len:int.
       ropes_sub_inv string_length (RopesSubApp left right len) =
       ((&0:int) < ropes_sub_length left /\
        ropes_sub_inv string_length left /\
        (&0:int) < ropes_sub_length right /\
        ropes_sub_inv string_length right /\
        len = ropes_sub_length left + ropes_sub_length right))`;;

let ropes_sub_string =
  new_recursive_definition ropes_sub_rope_RECURSION
   `(!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
       ropes_sub_string empty string_sub string_app
         (RopesSubEmp:S ropes_sub_rope) = empty) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !s:S.
     !ofs len:int.
       ropes_sub_string empty string_sub string_app
         (RopesSubStr s ofs len) =
       string_sub s ofs len) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !left right:S ropes_sub_rope.
     !len:int.
       ropes_sub_string empty string_sub string_app
         (RopesSubApp left right len) =
       string_app
         (ropes_sub_string empty string_sub string_app left)
         (ropes_sub_string empty string_sub string_app right))`;;

let ropes_sub_string_equal = new_definition
 `ropes_sub_string_equal
    (string_length:S->int)
    (string_index:S->int->C)
    (left:S) (right:S) <=>
    string_length left = string_length right /\
    (!i:int.
       (&0:int) <= i /\ i < string_length left
       ==> string_index left i = string_index right i)`;;

let ropes_sub_string_context = new_definition
 `ropes_sub_string_context
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S) <=>
    (!s:S. (&0:int) <= string_length s) /\
    string_length empty = (&0:int) /\
    (!left right:S.
       ropes_sub_string_equal string_length string_index left right
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
           string_index s (ofs + i))`;;

let ropes_sub_immediate_child =
  new_recursive_definition ropes_sub_rope_RECURSION
   `(!child:S ropes_sub_rope.
       ropes_sub_immediate_child
         (RopesSubEmp:S ropes_sub_rope) child = F) /\
    (!s:S. !ofs len:int. !child:S ropes_sub_rope.
       ropes_sub_immediate_child
         (RopesSubStr s ofs len) child = F) /\
    (!left right:S ropes_sub_rope. !len:int.
     !child:S ropes_sub_rope.
       ropes_sub_immediate_child
         (RopesSubApp left right len) child =
       (left = child \/ right = child))`;;

let ropes_sub_app_branch_precondition = new_definition
 `ropes_sub_app_branch_precondition
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S)
    (left:S ropes_sub_rope)
    (right:S ropes_sub_rope)
    (stored_len:int)
    (len:int)
    (ofs:int) <=>
    let left_part = ropes_sub_length left - ofs in
    let right_part = len - left_part in
    if right_part <= (&0:int) then
      ropes_sub_immediate_child
        (RopesSubApp left right stored_len) left /\
      ropes_sub_inv string_length left /\
      (&0:int) <= len /\
      ((&0:int) <= ofs /\ ofs <= ropes_sub_length left) /\
      ofs + len <= ropes_sub_length left
    else if left_part <= (&0:int) then
      let offset = (&0:int) - left_part in
      ropes_sub_immediate_child
        (RopesSubApp left right stored_len) right /\
      ropes_sub_inv string_length right /\
      (&0:int) <= len /\
      ((&0:int) <= offset /\ offset <= ropes_sub_length right) /\
      offset + len <= ropes_sub_length right
    else
      (ropes_sub_immediate_child
         (RopesSubApp left right stored_len) right /\
       ropes_sub_inv string_length right /\
       (&0:int) <= right_part /\
       ((&0:int) <= (&0:int) /\
        (&0:int) <= ropes_sub_length right) /\
       (&0:int) + right_part <= ropes_sub_length right) /\
      (!right_result:S ropes_sub_rope.
         ropes_sub_inv string_length right_result /\
         ropes_sub_string_equal string_length string_index
           (ropes_sub_string
             empty string_sub string_app right_result)
           (string_sub
             (ropes_sub_string
               empty string_sub string_app right)
             (&0:int) right_part)
         ==>
         (ropes_sub_immediate_child
            (RopesSubApp left right stored_len) left /\
          ropes_sub_inv string_length left /\
          (&0:int) <= left_part /\
          ((&0:int) <= ofs /\ ofs <= ropes_sub_length left) /\
          ofs + left_part <= ropes_sub_length left) /\
         (!left_result:S ropes_sub_rope.
            ropes_sub_inv string_length left_result /\
            ropes_sub_string_equal string_length string_index
              (ropes_sub_string
                empty string_sub string_app left_result)
              (string_sub
                (ropes_sub_string
                  empty string_sub string_app left)
                ofs left_part)
            ==>
            ropes_sub_inv string_length left_result /\
            ropes_sub_inv string_length right_result))`;;

let ropes_sub_branch_precondition =
  new_recursive_definition ropes_sub_rope_RECURSION
   `(!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !len ofs:int.
       ropes_sub_branch_precondition
         string_length string_index empty string_app string_sub
         (RopesSubEmp:S ropes_sub_rope) len ofs = T) /\
    (!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !s:S.
     !stored_ofs stored_len len ofs:int.
       ropes_sub_branch_precondition
         string_length string_index empty string_app string_sub
         (RopesSubStr s stored_ofs stored_len) len ofs = T) /\
    (!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !left right:S ropes_sub_rope.
     !stored_len len ofs:int.
       ropes_sub_branch_precondition
         string_length string_index empty string_app string_sub
         (RopesSubApp left right stored_len) len ofs =
       ropes_sub_app_branch_precondition
         string_length string_index empty string_app string_sub
         left right stored_len len ofs)`;;

let ropes_sub_app_result_condition = new_definition
 `ropes_sub_app_result_condition
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S)
    (result:S ropes_sub_rope)
    (left:S ropes_sub_rope)
    (right:S ropes_sub_rope)
    (stored_len:int)
    (len:int)
    (ofs:int) <=>
    let left_part = ropes_sub_length left - ofs in
    let right_part = len - left_part in
    if right_part <= (&0:int) then
      ropes_sub_inv string_length result /\
      ropes_sub_string_equal string_length string_index
        (ropes_sub_string empty string_sub string_app result)
        (string_sub
          (ropes_sub_string empty string_sub string_app left)
          ofs len)
    else if left_part <= (&0:int) then
      ropes_sub_inv string_length result /\
      ropes_sub_string_equal string_length string_index
        (ropes_sub_string empty string_sub string_app result)
        (string_sub
          (ropes_sub_string empty string_sub string_app right)
          ((&0:int) - left_part) len)
    else
      ?right_result:S ropes_sub_rope.
        (ropes_sub_inv string_length right_result /\
         ropes_sub_string_equal string_length string_index
           (ropes_sub_string
             empty string_sub string_app right_result)
           (string_sub
             (ropes_sub_string
               empty string_sub string_app right)
             (&0:int) right_part)) /\
        (?left_result:S ropes_sub_rope.
           (ropes_sub_inv string_length left_result /\
            ropes_sub_string_equal string_length string_index
              (ropes_sub_string
                empty string_sub string_app left_result)
              (string_sub
                (ropes_sub_string
                  empty string_sub string_app left)
                ofs left_part)) /\
           ropes_sub_inv string_length result /\
           ropes_sub_string_equal string_length string_index
             (ropes_sub_string
               empty string_sub string_app result)
             (string_app
               (ropes_sub_string
                 empty string_sub string_app left_result)
               (ropes_sub_string
                 empty string_sub string_app right_result)))`;;

let ropes_sub_result_condition =
  new_recursive_definition ropes_sub_rope_RECURSION
   `(!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !result:S ropes_sub_rope.
     !len ofs:int.
       ropes_sub_result_condition
         string_length string_index empty string_app string_sub
         result (RopesSubEmp:S ropes_sub_rope) len ofs =
       (result = RopesSubEmp)) /\
    (!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !result:S ropes_sub_rope.
     !s:S.
     !stored_ofs stored_len len ofs:int.
       ropes_sub_result_condition
         string_length string_index empty string_app string_sub
         result (RopesSubStr s stored_ofs stored_len) len ofs =
       (if len = (&0:int)
        then result = RopesSubEmp
        else result = RopesSubStr s (stored_ofs + ofs) len)) /\
    (!string_length:S->int.
     !string_index:S->int->C.
     !empty:S.
     !string_app:S->S->S.
     !string_sub:S->int->int->S.
     !result:S ropes_sub_rope.
     !left right:S ropes_sub_rope.
     !stored_len len ofs:int.
       ropes_sub_result_condition
         string_length string_index empty string_app string_sub
         result (RopesSubApp left right stored_len) len ofs =
       ropes_sub_app_result_condition
         string_length string_index empty string_app string_sub
         result left right stored_len len ofs)`;;

let statement =
 `!string_length:S->int.
  !string_index:S->int->C.
  !empty:S.
  !string_app:S->S->S.
  !string_sub:S->int->int->S.
    ropes_sub_string_context
      string_length string_index empty string_app string_sub
    ==>
    !r:S ropes_sub_rope.
    !len ofs:int.
      ropes_sub_inv string_length r
      ==>
      (&0:int) <= len
      ==>
      (&0:int) <= ofs
      ==>
      ofs <= ropes_sub_length r
      ==>
      ofs + len <= ropes_sub_length r
      ==>
      ropes_sub_branch_precondition
        string_length string_index empty string_app string_sub r len ofs /\
      (!result:S ropes_sub_rope.
         ropes_sub_result_condition
           string_length string_index empty string_app string_sub
           result r len ofs
         ==>
         ropes_sub_inv string_length result /\
         ropes_sub_string_equal string_length string_index
           (ropes_sub_string empty string_sub string_app result)
           (string_sub
             (ropes_sub_string empty string_sub string_app r)
             ofs len))`;;
