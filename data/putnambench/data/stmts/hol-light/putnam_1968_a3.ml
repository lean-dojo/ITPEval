(*
  Statement-only formalization of PutnamBench artifact putnam_1968_a3:
  a Gray-code ordering of all subsets of any finite set, beginning with the
  empty set and changing one element at each step. This file contains no proof.
*)

let statement =
  `!u:A->bool.
     FINITE u
     ==> ?l:(A->bool)list.
           EL 0 l = {} /\
           (!i:num. i < LENGTH l ==> EL i l SUBSET u) /\
           (!s:A->bool.
              s SUBSET u
              ==> ?!i:num. i < LENGTH l /\ EL i l = s) /\
           (!i:num.
              i + 1 < LENGTH l
              ==> (((EL i l) DIFF (EL (i + 1) l)) UNION
                   ((EL (i + 1) l) DIFF (EL i l))) HAS_SIZE 1)`;;
