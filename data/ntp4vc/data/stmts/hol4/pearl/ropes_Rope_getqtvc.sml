(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Rope_getqtvc: the rope character-access verification condition,
  establishing recursive branch bounds and agreement with the indexed
  character of the modeled string. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory;

Datatype:
  ropes_rope =
    RopesEmp
  | RopesStr 'string int int
  | RopesApp ropes_rope ropes_rope int
End

val ropes_string_equal_def = Define `
  ropes_string_equal string_length string_index s1 s2 <=>
    string_length s1 = string_length s2 /\
    !i : int.
      0 <= i /\ i < string_length s1 ==>
      string_index s1 i = string_index s2 i`;

val ropes_length_def = Define `
  (ropes_length RopesEmp = (0 : int)) /\
  (ropes_length (RopesStr s offset len) = len) /\
  (ropes_length (RopesApp left right len) = len)`;

val ropes_inv_def = Define `
  (ropes_inv string_length RopesEmp = T) /\
  (ropes_inv string_length (RopesStr s offset len) =
     ((0 : int) < len /\
      0 <= offset /\
      offset < string_length s /\
      offset + len <= string_length s)) /\
  (ropes_inv string_length (RopesApp left right len) =
     ((0 : int) < ropes_length left /\
      ropes_inv string_length left /\
      (0 : int) < ropes_length right /\
      ropes_inv string_length right /\
      len = ropes_length left + ropes_length right))`;

val ropes_string_def = Define `
  (ropes_string empty_string string_app string_sub RopesEmp =
     empty_string) /\
  (ropes_string empty_string string_app string_sub
      (RopesStr s offset len) =
     string_sub s offset len) /\
  (ropes_string empty_string string_app string_sub
      (RopesApp left right len) =
     string_app
       (ropes_string empty_string string_app string_sub left)
       (ropes_string empty_string string_app string_sub right))`;

val ropes_contains_child_def = Define `
  (ropes_contains_child RopesEmp child = F) /\
  (ropes_contains_child (RopesStr s offset len) child = F) /\
  (ropes_contains_child (RopesApp left right len) child =
     (left = child \/ right = child))`;

val ropes_branch_obligation_def = Define `
  (ropes_branch_obligation string_length RopesEmp i = F) /\
  (ropes_branch_obligation string_length
      (RopesStr s offset len) i =
     (let o1 = offset + i
      in (0 : int) <= o1 /\ o1 < string_length s)) /\
  (ropes_branch_obligation string_length
      (RopesApp left right len) i =
     (let n = ropes_length left
      in
        if i < n then
          ropes_contains_child (RopesApp left right len) left /\
          ropes_inv string_length left /\
          (0 : int) <= i /\
          i < ropes_length left
        else
          let o1 = i - n
          in
            ropes_contains_child (RopesApp left right len) right /\
            ropes_inv string_length right /\
            (0 : int) <= o1 /\
            o1 < ropes_length right))`;

val ropes_result_premise_def = Define `
  (ropes_result_premise string_index empty_string string_app string_sub
      RopesEmp i result = F) /\
  (ropes_result_premise string_index empty_string string_app string_sub
      (RopesStr s offset len) i result =
     (result = string_index s (offset + i))) /\
  (ropes_result_premise string_index empty_string string_app string_sub
      (RopesApp left right len) i result =
     (let n = ropes_length left
      in
        if i < n then
          result =
            string_index
              (ropes_string empty_string string_app string_sub left) i
        else
          result =
            string_index
              (ropes_string empty_string string_app string_sub right)
              (i - n)))`;

val ropes_Rope_getqtvc_statement =
  ``!(string_length : 'string -> int)
      (string_index : 'string -> int -> 'char)
      (empty_string : 'string)
      (string_app : 'string -> 'string -> 'string)
      (string_sub : 'string -> int -> int -> 'string)
      (r : 'string ropes_rope)
      (i : int).
      (!s. (0 : int) <= string_length s) ==>
      string_length empty_string = (0 : int) ==>
      (!s1 s2.
         ropes_string_equal string_length string_index s1 s2 ==>
         s1 = s2) ==>
      (!s1 s2.
         string_length (string_app s1 s2) =
           string_length s1 + string_length s2) ==>
      (!s1 s2 j.
         (0 : int) <= j /\ j < string_length s1 ==>
         string_index (string_app s1 s2) j =
           string_index s1 j) ==>
      (!s1 s2 j.
         string_length s1 <= j /\
         j < string_length s1 + string_length s2 ==>
         string_index (string_app s1 s2) j =
           string_index s2 (j - string_length s1)) ==>
      (!s offset len.
         (0 : int) <= len /\
         (0 : int) <= offset /\
         offset <= string_length s /\
         offset + len <= string_length s ==>
         string_length (string_sub s offset len) = len) ==>
      (!s offset len j.
         (0 : int) <= len /\
         (0 : int) <= offset /\
         offset <= string_length s /\
         offset + len <= string_length s /\
         (0 : int) <= j /\
         j < len ==>
         string_index (string_sub s offset len) j =
           string_index s (offset + j)) ==>
      ropes_inv string_length r ==>
      (0 : int) <= i ==>
      i < ropes_length r ==>
      ropes_branch_obligation string_length r i /\
      !result : 'char.
        ropes_result_premise
          string_index empty_string string_app string_sub r i result
        ==>
        result =
          string_index
            (ropes_string empty_string string_app string_sub r) i``;
