(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b3:
  exactly three integer-sided right triangles with ordered positive legs
  whose area is twice their perimeter. This file contains no proof.
*)

let statement =
  `CARD
     {(a,b,c):int#int#int |
        (&0:int) < a /\
        a <= b /\
        (&0:int) < c /\
        a pow 2 + b pow 2 = c pow 2 /\
        real_of_int a * real_of_int b / &2 =
        &2 * (real_of_int a + real_of_int b + real_of_int c)} =
   3`;;
