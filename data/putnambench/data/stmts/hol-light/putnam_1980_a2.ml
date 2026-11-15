(*
  Statement-only formalization of PutnamBench artifact putnam_1980_a2:
  the number of ordered positive-integer quadruples whose four triple least
  common multiples equal 3^r * 7^s. This file contains no proof.
*)

let statement =
  `let putnam_1980_a2_solution =
     \r s:num.
       (1 + 4 * r + 6 * r EXP 2) *
       (1 + 4 * s + 6 * s EXP 2) in
   !r s:num.
     0 < r /\ 0 < s
     ==> {(a,b,c,d):num#num#num#num |
            0 < a /\ 0 < b /\ 0 < c /\ 0 < d /\
            3 EXP r * 7 EXP s = lcm(lcm(a,b),c) /\
            3 EXP r * 7 EXP s = lcm(lcm(a,b),d) /\
            3 EXP r * 7 EXP s = lcm(lcm(a,c),d) /\
            3 EXP r * 7 EXP s = lcm(lcm(b,c),d)}
         HAS_SIZE putnam_1980_a2_solution r s`;;
