(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Balance_insert_leavesqtvc: the verification condition for
  recursively inserting a rope's leaves into a balanced-rope queue while
  preserving its invariant and modeled string. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory listTheory;

Datatype:
  ropes_rope =
    RopesEmp
  | RopesStr 'string int int
  | RopesApp ropes_rope ropes_rope int
End

val ropes_to_num_def = Define `
  ropes_to_num (z : int) =
    if z < 0 then 0 else Num z`;

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

val ropes_string_of_queue_def = Define `
  ropes_string_of_queue string_of_array q =
    string_of_array q (2 : int) (&(LENGTH q))`;

val ropes_Balance_insert_leavesqtvc_statement =
  ``!(string_length : 'string -> int)
      (string_index : 'string -> int -> 'char)
      (empty_string : 'string)
      (string_app : 'string -> 'string -> 'string)
      (string_sub : 'string -> int -> int -> 'string)
      (fib : int -> int)
      (maximum : int)
      (string_of_array :
        ('string ropes_rope) list -> int -> int -> 'string)
      (q : ('string ropes_rope) list)
      (r : 'string ropes_rope).
      (!s. (0 : int) <= string_length s) ==>
      string_length empty_string = (0 : int) ==>
      (!s1 s2.
         ropes_string_equal string_length string_index s1 s2 ==>
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
      (!s offset len.
         (0 : int) <= len /\
         (0 : int) <= offset /\
         offset <= string_length s /\
         offset + len <= string_length s ==>
         string_length (string_sub s offset len) = len) ==>
      (!s offset len i.
         (0 : int) <= len /\
         (0 : int) <= offset /\
         offset <= string_length s /\
         offset + len <= string_length s /\
         (0 : int) <= i /\
         i < len ==>
         string_index (string_sub s offset len) i =
           string_index s (offset + i)) ==>
      (!n.
         (0 : int) <= n ==>
         fib n =
           if n = 0 then 0
           else if n = 1 then 1
           else fib (n - 1) + fib (n - 2)) ==>
      (2 : int) <= maximum ==>
      (!l q0.
         (0 : int) <= l /\ l <= &(LENGTH q0) ==>
         ropes_string_equal string_length string_index
           (string_of_array q0 l l)
           empty_string) ==>
      (!l u q0.
         (0 : int) <= l /\ l < u /\ u <= &(LENGTH q0) ==>
         ropes_string_equal string_length string_index
           (string_of_array q0 l u)
           (string_app
             (string_of_array q0 (l + 1) u)
             (ropes_string empty_string string_app string_sub
               (EL (ropes_to_num l) q0)))) ==>
      (2 : int) < &(LENGTH q) ==>
      &(LENGTH q) = maximum + (1 : int) ==>
      ropes_inv string_length r ==>
      (!j : int.
         (2 : int) <= j /\ j <= maximum ==>
         ropes_inv string_length
           (EL (ropes_to_num j) q)) ==>
      string_length (ropes_string_of_queue string_of_array q) +
        ropes_length r <
          fib (maximum + 1) ==>
      case r of
        RopesEmp =>
          (!j : int.
             (2 : int) <= j /\ j <= maximum ==>
             ropes_inv string_length
               (EL (ropes_to_num j) q)) /\
          ropes_string_equal string_length string_index
            (ropes_string_of_queue string_of_array q)
            (string_app
              (ropes_string_of_queue string_of_array q)
              (ropes_string
                empty_string string_app string_sub r))
      | RopesStr s offset len =>
          (((2 : int) <= (2 : int) /\
            (2 : int) < &(LENGTH q) /\
            &(LENGTH q) = maximum + 1) /\
           ropes_inv string_length r /\
           (!j : int.
              (2 : int) <= j /\ j <= maximum ==>
              ropes_inv string_length
                (EL (ropes_to_num j) q)) /\
           string_length
               (string_of_array q (2 : int) (maximum + 1)) +
             ropes_length r <
               fib (maximum + 1)) /\
          !q1 : ('string ropes_rope) list.
            LENGTH q1 = LENGTH q ==>
            (((!j : int.
                 (2 : int) <= j /\ j <= maximum ==>
                 ropes_inv string_length
                   (EL (ropes_to_num j) q1)) /\
              (!j : int.
                 (2 : int) <= j /\ j < (2 : int) ==>
                 EL (ropes_to_num j) q1 =
                   EL (ropes_to_num j) q) /\
              ropes_string_equal string_length string_index
                (string_of_array q1 (2 : int) (maximum + 1))
                (string_app
                  (string_of_array q (2 : int) (maximum + 1))
                  (ropes_string
                    empty_string string_app string_sub r))) ==>
             (!j : int.
                (2 : int) <= j /\ j <= maximum ==>
                ropes_inv string_length
                  (EL (ropes_to_num j) q1)) /\
             ropes_string_equal string_length string_index
               (ropes_string_of_queue string_of_array q1)
               (string_app
                 (ropes_string_of_queue string_of_array q)
                 (ropes_string
                   empty_string string_app string_sub r)))
      | RopesApp left1 right1 total_len =>
          ((case r of
              RopesEmp => F
            | RopesStr s offset len => F
            | RopesApp f f1 len => f = left1 \/ f1 = left1) /\
           ((2 : int) < &(LENGTH q) /\
            &(LENGTH q) = maximum + 1) /\
           ropes_inv string_length left1 /\
           (!j : int.
              (2 : int) <= j /\ j <= maximum ==>
              ropes_inv string_length
                (EL (ropes_to_num j) q)) /\
           string_length
               (ropes_string_of_queue string_of_array q) +
             ropes_length left1 <
               fib (maximum + 1)) /\
          !q1 : ('string ropes_rope) list.
            LENGTH q1 = LENGTH q ==>
            (((!j : int.
                 (2 : int) <= j /\ j <= maximum ==>
                 ropes_inv string_length
                   (EL (ropes_to_num j) q1)) /\
              ropes_string_equal string_length string_index
                (ropes_string_of_queue string_of_array q1)
                (string_app
                  (ropes_string_of_queue string_of_array q)
                  (ropes_string
                    empty_string string_app string_sub left1))) ==>
             ((case r of
                 RopesEmp => F
               | RopesStr s offset len => F
               | RopesApp f f1 len =>
                   f = right1 \/ f1 = right1) /\
              ((2 : int) < &(LENGTH q1) /\
               &(LENGTH q1) = maximum + 1) /\
              ropes_inv string_length right1 /\
              (!j : int.
                 (2 : int) <= j /\ j <= maximum ==>
                 ropes_inv string_length
                   (EL (ropes_to_num j) q1)) /\
              string_length
                  (ropes_string_of_queue string_of_array q1) +
                ropes_length right1 <
                  fib (maximum + 1)) /\
             !q2 : ('string ropes_rope) list.
               LENGTH q2 = LENGTH q1 ==>
               (((!j : int.
                    (2 : int) <= j /\ j <= maximum ==>
                    ropes_inv string_length
                      (EL (ropes_to_num j) q2)) /\
                 ropes_string_equal string_length string_index
                   (ropes_string_of_queue string_of_array q2)
                   (string_app
                     (ropes_string_of_queue string_of_array q1)
                     (ropes_string
                       empty_string string_app string_sub right1))) ==>
                (!j : int.
                   (2 : int) <= j /\ j <= maximum ==>
                   ropes_inv string_length
                     (EL (ropes_to_num j) q2)) /\
                ropes_string_equal string_length string_index
                  (ropes_string_of_queue string_of_array q2)
                  (string_app
                    (ropes_string_of_queue string_of_array q)
                    (ropes_string
                      empty_string string_app string_sub r)))``;
