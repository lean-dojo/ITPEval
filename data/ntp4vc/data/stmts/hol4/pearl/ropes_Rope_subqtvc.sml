(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Rope_subqtvc: the recursive rope substring verification
  condition, including branch bounds, rope invariants, and agreement of the
  resulting rope with the modeled string substring. This file contains no
  proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  rope_sub_rope =
    RopeSubEmp
  | RopeSubStr 'string int int
  | RopeSubApp rope_sub_rope rope_sub_rope int
End

val rope_sub_string_equal_def = Define `
  rope_sub_string_equal string_length string_index s1 s2 <=>
    string_length s1 = string_length s2 /\
    !i : int.
      (0 : int) <= i /\ i < string_length s1 ==>
      string_index s1 i = string_index s2 i`;

val rope_sub_length_def = Define `
  (rope_sub_length RopeSubEmp = (0 : int)) /\
  (rope_sub_length (RopeSubStr s offset len) = len) /\
  (rope_sub_length (RopeSubApp left right len) = len)`;

val rope_sub_inv_def = Define `
  (rope_sub_inv string_length RopeSubEmp = T) /\
  (rope_sub_inv string_length (RopeSubStr s offset len) =
     ((0 : int) < len /\
      (0 : int) <= offset /\
      offset < string_length s /\
      offset + len <= string_length s)) /\
  (rope_sub_inv string_length (RopeSubApp left right len) =
     ((0 : int) < rope_sub_length left /\
      rope_sub_inv string_length left /\
      (0 : int) < rope_sub_length right /\
      rope_sub_inv string_length right /\
      len = rope_sub_length left + rope_sub_length right))`;

val rope_sub_string_def = Define `
  (rope_sub_string empty_string string_app string_sub RopeSubEmp =
     empty_string) /\
  (rope_sub_string empty_string string_app string_sub
      (RopeSubStr s offset len) =
     string_sub s offset len) /\
  (rope_sub_string empty_string string_app string_sub
      (RopeSubApp left right len) =
     string_app
       (rope_sub_string empty_string string_app string_sub left)
       (rope_sub_string empty_string string_app string_sub right))`;

val rope_sub_contains_child_def = Define `
  (rope_sub_contains_child RopeSubEmp child = F) /\
  (rope_sub_contains_child (RopeSubStr s offset len) child = F) /\
  (rope_sub_contains_child (RopeSubApp left right len) child =
     (left = child \/ right = child))`;

val rope_sub_branch_obligation_def = Define `
  (rope_sub_branch_obligation
      string_length string_index empty_string string_app string_sub
      RopeSubEmp len offset = T) /\
  (rope_sub_branch_obligation
      string_length string_index empty_string string_app string_sub
      (RopeSubStr s stored_offset stored_len) len offset = T) /\
  (rope_sub_branch_obligation
      string_length string_index empty_string string_app string_sub
      (RopeSubApp left right total_len) len offset =
     (let left_len = rope_sub_length left - offset;
          right_len = len - left_len
      in
        if right_len <= (0 : int) then
          rope_sub_contains_child
            (RopeSubApp left right total_len) left /\
          rope_sub_inv string_length left /\
          (0 : int) <= len /\
          ((0 : int) <= offset /\ offset <= rope_sub_length left) /\
          offset + len <= rope_sub_length left
        else if left_len <= (0 : int) then
          let right_offset = -left_len
          in
            rope_sub_contains_child
              (RopeSubApp left right total_len) right /\
            rope_sub_inv string_length right /\
            (0 : int) <= len /\
            ((0 : int) <= right_offset /\
             right_offset <= rope_sub_length right) /\
            right_offset + len <= rope_sub_length right
        else
          (rope_sub_contains_child
             (RopeSubApp left right total_len) right /\
           rope_sub_inv string_length right /\
           (0 : int) <= right_len /\
           ((0 : int) <= (0 : int) /\
            (0 : int) <= rope_sub_length right) /\
           (0 : int) + right_len <= rope_sub_length right) /\
          !right_result : 'string rope_sub_rope.
            rope_sub_inv string_length right_result /\
            rope_sub_string_equal string_length string_index
              (rope_sub_string
                empty_string string_app string_sub right_result)
              (string_sub
                (rope_sub_string empty_string string_app string_sub right)
                (0 : int) right_len)
            ==>
            (rope_sub_contains_child
               (RopeSubApp left right total_len) left /\
             rope_sub_inv string_length left /\
             (0 : int) <= left_len /\
             ((0 : int) <= offset /\ offset <= rope_sub_length left) /\
             offset + left_len <= rope_sub_length left) /\
            !left_result : 'string rope_sub_rope.
              rope_sub_inv string_length left_result /\
              rope_sub_string_equal string_length string_index
                (rope_sub_string
                  empty_string string_app string_sub left_result)
                (string_sub
                  (rope_sub_string empty_string string_app string_sub left)
                  offset left_len)
              ==>
              rope_sub_inv string_length left_result /\
              rope_sub_inv string_length right_result))`;

val rope_sub_result_premise_def = Define `
  (rope_sub_result_premise
      string_length string_index empty_string string_app string_sub
      RopeSubEmp len offset result =
     (result = RopeSubEmp)) /\
  (rope_sub_result_premise
      string_length string_index empty_string string_app string_sub
      (RopeSubStr s stored_offset stored_len) len offset result =
     (if len = (0 : int) then
        result = RopeSubEmp
      else
        result = RopeSubStr s (stored_offset + offset) len)) /\
  (rope_sub_result_premise
      string_length string_index empty_string string_app string_sub
      (RopeSubApp left right total_len) len offset result =
     (let left_len = rope_sub_length left - offset;
          right_len = len - left_len
      in
        if right_len <= (0 : int) then
          rope_sub_inv string_length result /\
          rope_sub_string_equal string_length string_index
            (rope_sub_string empty_string string_app string_sub result)
            (string_sub
              (rope_sub_string empty_string string_app string_sub left)
              offset len)
        else if left_len <= (0 : int) then
          rope_sub_inv string_length result /\
          rope_sub_string_equal string_length string_index
            (rope_sub_string empty_string string_app string_sub result)
            (string_sub
              (rope_sub_string empty_string string_app string_sub right)
              (-left_len) len)
        else
          ?right_result : 'string rope_sub_rope.
            (rope_sub_inv string_length right_result /\
             rope_sub_string_equal string_length string_index
               (rope_sub_string
                 empty_string string_app string_sub right_result)
               (string_sub
                 (rope_sub_string empty_string string_app string_sub right)
                 (0 : int) right_len)) /\
            ?left_result : 'string rope_sub_rope.
              (rope_sub_inv string_length left_result /\
               rope_sub_string_equal string_length string_index
                 (rope_sub_string
                   empty_string string_app string_sub left_result)
                 (string_sub
                   (rope_sub_string empty_string string_app string_sub left)
                   offset left_len)) /\
              rope_sub_inv string_length result /\
              rope_sub_string_equal string_length string_index
                (rope_sub_string
                  empty_string string_app string_sub result)
                (string_app
                  (rope_sub_string
                    empty_string string_app string_sub left_result)
                  (rope_sub_string
                    empty_string string_app string_sub right_result))))`;

val ropes_Rope_subqtvc_statement =
  ``!(string_length : 'string -> int)
      (string_index : 'string -> int -> 'char)
      (empty_string : 'string)
      (string_app : 'string -> 'string -> 'string)
      (string_sub : 'string -> int -> int -> 'string)
      (r : 'string rope_sub_rope)
      (len : int)
      (offset : int).
      (!s. (0 : int) <= string_length s) ==>
      string_length empty_string = (0 : int) ==>
      (!s1 s2.
         rope_sub_string_equal string_length string_index s1 s2 ==>
         s1 = s2) ==>
      (!s1 s2.
         string_length (string_app s1 s2) =
           string_length s1 + string_length s2) ==>
      (!s1 s2 i.
         (0 : int) <= i /\ i < string_length s1 ==>
         string_index (string_app s1 s2) i =
           string_index s1 i) ==>
      (!s1 s2 i.
         string_length s1 <= i /\
         i < string_length s1 + string_length s2 ==>
         string_index (string_app s1 s2) i =
           string_index s2 (i - string_length s1)) ==>
      (!s substring_offset substring_len.
         (0 : int) <= substring_len /\
         (0 : int) <= substring_offset /\
         substring_offset <= string_length s /\
         substring_offset + substring_len <= string_length s ==>
         string_length
           (string_sub s substring_offset substring_len) =
           substring_len) ==>
      (!s substring_offset substring_len i.
         (0 : int) <= substring_len /\
         (0 : int) <= substring_offset /\
         substring_offset <= string_length s /\
         substring_offset + substring_len <= string_length s /\
         (0 : int) <= i /\
         i < substring_len ==>
         string_index
           (string_sub s substring_offset substring_len) i =
           string_index s (substring_offset + i)) ==>
      rope_sub_inv string_length r ==>
      (0 : int) <= len ==>
      (0 : int) <= offset ==>
      offset <= rope_sub_length r ==>
      offset + len <= rope_sub_length r ==>
      rope_sub_branch_obligation
        string_length string_index empty_string string_app string_sub
        r len offset /\
      !result : 'string rope_sub_rope.
        rope_sub_result_premise
          string_length string_index empty_string string_app string_sub
          r len offset result
        ==>
        rope_sub_inv string_length result /\
        rope_sub_string_equal string_length string_index
          (rope_sub_string empty_string string_app string_sub result)
          (string_sub
            (rope_sub_string empty_string string_app string_sub r)
            offset len)``;
