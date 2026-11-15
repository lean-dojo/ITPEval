(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/ropes_Balance_insertqtvc: the rope queue insertion verification
  condition for direct update and recursive carry while preserving rope
  invariants, unchanged prefixes, and modeled-string concatenation. This file
  contains no proof.
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

val ropes_get_def = Define `
  ropes_get (q : ('string ropes_rope) list) (i : int) =
    EL (ropes_to_num i) q`;

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

val ropes_Balance_insertqtvc_statement =
  ``!(string_length : 'string -> int)
      (string_index : 'string -> int -> 'char)
      (empty_string : 'string)
      (string_app : 'string -> 'string -> 'string)
      (string_sub : 'string -> int -> int -> 'string)
      (fib : int -> int)
      (maximum : int)
      (string_of_array :
        ('string ropes_rope) list -> int -> int -> 'string)
      (i : int)
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
               (ropes_get q0 l)))) ==>
      (2 : int) <= i ==>
      i < &(LENGTH q) ==>
      &(LENGTH q) = maximum + (1 : int) ==>
      ropes_inv string_length r ==>
      (!j : int.
         (2 : int) <= j /\ j <= maximum ==>
         ropes_inv string_length (ropes_get q j)) ==>
      string_length (string_of_array q i (maximum + 1)) +
        ropes_length r <
          fib (maximum + 1) ==>
      ((0 : int) <= i /\ i < &(LENGTH q)) /\
      let o1 = ropes_get q i
      in
        (ropes_inv string_length o1 /\
         ropes_inv string_length r) /\
        !r' : 'string ropes_rope.
          ropes_inv string_length r' /\
          ropes_string_equal string_length string_index
            (ropes_string empty_string string_app string_sub r')
            (string_app
              (ropes_string empty_string string_app string_sub o1)
              (ropes_string empty_string string_app string_sub r))
          ==>
          let o2 = i + (1 : int)
          in
            (0 : int) <= o2 /\
            if ropes_length r' < fib o2 then
              ((0 : int) <= i /\ i < &(LENGTH q)) /\
              (LENGTH (LUPDATE r' (ropes_to_num i) q) = LENGTH q
               ==>
               (\z : int.
                  ropes_get (LUPDATE r' (ropes_to_num i) q) z) =
                 (\z : int.
                    if z = i then r' else ropes_get q z)
               ==>
               (!j : int.
                  (2 : int) <= j /\ j <= maximum ==>
                  ropes_inv string_length
                    (ropes_get
                      (LUPDATE r' (ropes_to_num i) q) j)) /\
               (!j : int.
                  (2 : int) <= j /\ j < i ==>
                  ropes_get (LUPDATE r' (ropes_to_num i) q) j =
                    ropes_get q j) /\
               ropes_string_equal string_length string_index
                 (string_of_array
                   (LUPDATE r' (ropes_to_num i) q)
                   i (maximum + 1))
                 (string_app
                   (string_of_array q i (maximum + 1))
                   (ropes_string
                     empty_string string_app string_sub r)))
            else
              let o3 : 'string ropes_rope = RopesEmp
              in
                ((0 : int) <= i /\ i < &(LENGTH q)) /\
                (LENGTH (LUPDATE o3 (ropes_to_num i) q) = LENGTH q
                 ==>
                 (\z : int.
                    ropes_get (LUPDATE o3 (ropes_to_num i) q) z) =
                   (\z : int.
                      if z = i then o3 else ropes_get q z)
                 ==>
                 let o4 = i + (1 : int)
                 in
                   (((0 : int) <= maximum - i /\
                     maximum - o4 < maximum - i) /\
                    ((2 : int) <= o4 /\
                     o4 <
                       &(LENGTH
                          (LUPDATE o3 (ropes_to_num i) q)) /\
                     &(LENGTH
                         (LUPDATE o3 (ropes_to_num i) q)) =
                       maximum + 1) /\
                    ropes_inv string_length r' /\
                    (!j : int.
                       (2 : int) <= j /\ j <= maximum ==>
                       ropes_inv string_length
                         (ropes_get
                           (LUPDATE o3 (ropes_to_num i) q) j)) /\
                    string_length
                        (string_of_array
                          (LUPDATE o3 (ropes_to_num i) q)
                          o4 (maximum + 1)) +
                      ropes_length r' <
                        fib (maximum + 1)) /\
                   !q1 : ('string ropes_rope) list.
                     LENGTH q1 =
                       LENGTH (LUPDATE o3 (ropes_to_num i) q)
                     ==>
                     ((!j : int.
                         (2 : int) <= j /\ j <= maximum ==>
                         ropes_inv string_length
                           (ropes_get q1 j)) /\
                      (!j : int.
                         (2 : int) <= j /\ j < o4 ==>
                         ropes_get q1 j =
                           ropes_get
                             (LUPDATE o3 (ropes_to_num i) q) j) /\
                      ropes_string_equal string_length string_index
                        (string_of_array q1 o4 (maximum + 1))
                        (string_app
                          (string_of_array
                            (LUPDATE o3 (ropes_to_num i) q)
                            o4 (maximum + 1))
                          (ropes_string
                            empty_string string_app string_sub r')))
                     ==>
                     (!j : int.
                        (2 : int) <= j /\ j <= maximum ==>
                        ropes_inv string_length
                          (ropes_get q1 j)) /\
                     (!j : int.
                        (2 : int) <= j /\ j < i ==>
                        ropes_get q1 j = ropes_get q j) /\
                     ropes_string_equal string_length string_index
                       (string_of_array q1 i (maximum + 1))
                       (string_app
                         (string_of_array q i (maximum + 1))
                         (ropes_string
                           empty_string string_app string_sub r)))``;
