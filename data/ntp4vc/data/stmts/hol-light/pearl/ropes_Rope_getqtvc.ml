(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Rope_getqtvc: the rope indexing verification condition,
  establishing recursive bounds and agreement of the selected character with
  the rope's modeled string. This file contains no proof.
*)

let ropes_get_rope_INDUCT,ropes_get_rope_RECURSION = define_type
  "ropes_get_rope =
       RopesGetEmp
     | RopesGetStr S int int
     | RopesGetApp ropes_get_rope ropes_get_rope int";;

let ropes_get_length =
  new_recursive_definition ropes_get_rope_RECURSION
   `(ropes_get_length (RopesGetEmp:S ropes_get_rope) = (&0:int)) /\
    (!s:S. !ofs len:int.
       ropes_get_length (RopesGetStr s ofs len) = len) /\
    (!left right:S ropes_get_rope. !len:int.
       ropes_get_length (RopesGetApp left right len) = len)`;;

let ropes_get_inv =
  new_recursive_definition ropes_get_rope_RECURSION
   `(!string_length:S->int.
       ropes_get_inv string_length
         (RopesGetEmp:S ropes_get_rope) = T) /\
    (!string_length:S->int. !s:S. !ofs len:int.
       ropes_get_inv string_length (RopesGetStr s ofs len) =
       ((&0:int) < len /\
        ((&0:int) <= ofs /\ ofs < string_length s) /\
        ofs + len <= string_length s)) /\
    (!string_length:S->int.
     !left right:S ropes_get_rope.
     !len:int.
       ropes_get_inv string_length (RopesGetApp left right len) =
       ((&0:int) < ropes_get_length left /\
        ropes_get_inv string_length left /\
        (&0:int) < ropes_get_length right /\
        ropes_get_inv string_length right /\
        len = ropes_get_length left + ropes_get_length right))`;;

let ropes_get_string =
  new_recursive_definition ropes_get_rope_RECURSION
   `(!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
       ropes_get_string empty string_sub string_app
         (RopesGetEmp:S ropes_get_rope) = empty) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !s:S.
     !ofs len:int.
       ropes_get_string empty string_sub string_app
         (RopesGetStr s ofs len) =
       string_sub s ofs len) /\
    (!empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !left right:S ropes_get_rope.
     !len:int.
       ropes_get_string empty string_sub string_app
         (RopesGetApp left right len) =
       string_app
         (ropes_get_string empty string_sub string_app left)
         (ropes_get_string empty string_sub string_app right))`;;

let ropes_get_string_equal = new_definition
 `ropes_get_string_equal
    (string_length:S->int)
    (string_index:S->int->C)
    (left:S) (right:S) <=>
    string_length left = string_length right /\
    (!i:int.
       (&0:int) <= i /\ i < string_length left
       ==> string_index left i = string_index right i)`;;

let ropes_get_string_context = new_definition
 `ropes_get_string_context
    (string_length:S->int)
    (string_index:S->int->C)
    (empty:S)
    (string_app:S->S->S)
    (string_sub:S->int->int->S) <=>
    (!s:S. (&0:int) <= string_length s) /\
    string_length empty = (&0:int) /\
    (!left right:S.
       ropes_get_string_equal string_length string_index left right
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

let ropes_get_immediate_child =
  new_recursive_definition ropes_get_rope_RECURSION
   `(!child:S ropes_get_rope.
       ropes_get_immediate_child
         (RopesGetEmp:S ropes_get_rope) child = F) /\
    (!s:S. !ofs len:int. !child:S ropes_get_rope.
       ropes_get_immediate_child
         (RopesGetStr s ofs len) child = F) /\
    (!left right:S ropes_get_rope. !len:int.
     !child:S ropes_get_rope.
       ropes_get_immediate_child
         (RopesGetApp left right len) child =
       (left = child \/ right = child))`;;

let ropes_get_branch_precondition =
  new_recursive_definition ropes_get_rope_RECURSION
   `(!string_length:S->int. !i:int.
       ropes_get_branch_precondition string_length
         (RopesGetEmp:S ropes_get_rope) i = F) /\
    (!string_length:S->int. !s:S. !ofs len i:int.
       ropes_get_branch_precondition string_length
         (RopesGetStr s ofs len) i =
       (let offset = ofs + i in
        (&0:int) <= offset /\ offset < string_length s)) /\
    (!string_length:S->int.
     !left right:S ropes_get_rope.
     !len i:int.
       ropes_get_branch_precondition string_length
         (RopesGetApp left right len) i =
       (let left_length = ropes_get_length left in
        if i < left_length then
          ropes_get_immediate_child
            (RopesGetApp left right len) left /\
          ropes_get_inv string_length left /\
          (&0:int) <= i /\
          i < ropes_get_length left
        else
          let offset = i - left_length in
          ropes_get_immediate_child
            (RopesGetApp left right len) right /\
          ropes_get_inv string_length right /\
          (&0:int) <= offset /\
          offset < ropes_get_length right))`;;

let ropes_get_selected_character =
  new_recursive_definition ropes_get_rope_RECURSION
   `(!string_index:S->int->C.
     !empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !result:C.
     !i:int.
       ropes_get_selected_character
         string_index empty string_sub string_app result
         (RopesGetEmp:S ropes_get_rope) i = F) /\
    (!string_index:S->int->C.
     !empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !result:C.
     !s:S.
     !ofs len i:int.
       ropes_get_selected_character
         string_index empty string_sub string_app result
         (RopesGetStr s ofs len) i =
       (result = string_index s (ofs + i))) /\
    (!string_index:S->int->C.
     !empty:S.
     !string_sub:S->int->int->S.
     !string_app:S->S->S.
     !result:C.
     !left right:S ropes_get_rope.
     !len i:int.
       ropes_get_selected_character
         string_index empty string_sub string_app result
         (RopesGetApp left right len) i =
       (let left_length = ropes_get_length left in
        if i < left_length then
          result =
          string_index
            (ropes_get_string empty string_sub string_app left) i
        else
          result =
          string_index
            (ropes_get_string empty string_sub string_app right)
            (i - left_length)))`;;

let statement =
 `!string_length:S->int.
  !string_index:S->int->C.
  !empty:S.
  !string_app:S->S->S.
  !string_sub:S->int->int->S.
    ropes_get_string_context
      string_length string_index empty string_app string_sub
    ==>
    !r:S ropes_get_rope.
    !i:int.
      ropes_get_inv string_length r
      ==>
      (&0:int) <= i
      ==>
      i < ropes_get_length r
      ==>
      ropes_get_branch_precondition string_length r i /\
      (!result:C.
         ropes_get_selected_character
           string_index empty string_sub string_app result r i
         ==>
         result =
         string_index
           (ropes_get_string empty string_sub string_app r) i)`;;
