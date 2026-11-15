(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1989_a1:
  exactly one positive prime has an ordinary decimal expansion alternating
  1 and 0, beginning and ending with 1. This file contains no proof.
*)

let statement =
  `{p:num |
      0 < p /\
      prime p /\
      ?digits:num list.
        ODD (LENGTH digits) /\
        (!i:num.
           i < LENGTH digits
           ==> EL i digits = if EVEN i then 1 else 0) /\
        ITLIST (\d acc. d + 10 * acc) digits 0 = p}
   HAS_SIZE 1`;;
