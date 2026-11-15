(* Statement-only formalization of miniF2F valid problem
   numbertheory_prmdvsneqnsqmodpeq0. *)
let statement = `!n:int p:num.
    prime p
    ==> ((&p:int) divides n <=> num_of_int (n pow 2) MOD p = 0)
`;;
