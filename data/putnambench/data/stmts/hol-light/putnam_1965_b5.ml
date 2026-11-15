(*
  Statement-only formalization of PutnamBench artifact putnam_1965_b5:
  existence of a triangle-free simple graph with V vertices and E edges
  when 4 * E <= V^2. This file contains no proof.
*)

let statement =
  `!E V:num.
     4 * E <= V EXP 2
     ==> ?G:num->num->bool.
           (!x y:num. G x y ==> x < V /\ y < V) /\
           (!x:num. ~G x x) /\
           (!x y:num. G x y <=> G y x) /\
           CARD {(x,y):num#num | G x y} = 2 * E /\
           ~(?a b c:num. G b c /\ G c a /\ G a b)`;;
