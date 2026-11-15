(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2013_a3:
  a vanishing finite reciprocal sum with denominators 1 - x^(i+1) forces the
  associated real polynomial to have a root in (0,1). This file contains no
  proof.
*)

let statement =
  `!n:num. !a:num->real. !x:real.
     &0 < x /\ x < &1 /\
     sum (0..n) (\i. a i / (&1 - x pow (i + 1))) = &0
     ==> ?y:real.
           &0 < y /\ y < &1 /\
           sum (0..n) (\i. a i * y pow i) = &0`;;
