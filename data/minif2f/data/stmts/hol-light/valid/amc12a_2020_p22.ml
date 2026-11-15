(* Statement-only formalization of miniF2F valid problem amc12a_2020_p22. *)
let statement =
  `FINITE {n:num |
      5 divides n /\ lcm (FACT 5,n) = 5 * gcd (FACT 10,n)} /\
   CARD {n:num |
      5 divides n /\ lcm (FACT 5,n) = 5 * gcd (FACT 10,n)} = 48`;;
