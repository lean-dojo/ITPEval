(*
  Statement-only formalization of PutnamBench artifact putnam_1967_b2:
  lower bounds for the largest coefficients in two quadratic identities
  determined by convex combinations of real variables. This file contains
  no proof.
*)

let statement =
  `!p r A B C alpha beta gamma:real.
     &0 <= p /\ p <= &1 /\ &0 <= r /\ r <= &1 /\
     (!x y:real.
        (p * x + (&1 - p) * y) pow 2 =
        A * x pow 2 + B * x * y + C * y pow 2) /\
     (!x y:real.
        (p * x + (&1 - p) * y) * (r * x + (&1 - r) * y) =
        alpha * x pow 2 + beta * x * y + gamma * y pow 2)
     ==> max (max A B) C >= &4 / &9 /\
         max (max alpha beta) gamma >= &4 / &9`;;
