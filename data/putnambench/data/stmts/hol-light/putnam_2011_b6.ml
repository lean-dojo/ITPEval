(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2011_b6:
  for an odd prime p, at least (p + 1) / 2 residues below p make the
  factorial-coefficient polynomial sum nondivisible by p. This file contains
  no proof.
*)

let statement =
  `!p:num.
     ODD p /\ prime p
     ==>
     CARD
       {n:num |
          n < p /\
          ~(p divides
            nsum (0..p - 1) (\k. FACT k * n EXP k))}
     >= (p + 1) DIV 2`;;
