(* ========================================================================= *)
(* #85: divisibility by 3 rule                                               *)
(* ========================================================================= *)

needs "Library/prime.ml";;
needs "Library/pocklington.ml";;

let EXP_10_CONG_3 = `!n. (10 EXP n == 1) (mod 3)`;;

let SUM_CONG_3 = `!d n. (nsum(0..n) (\i. 10 EXP i * d(i)) == nsum(0..n) (\i. d i)) (mod 3)`;;

let DIVISIBILITY_BY_3 = `3 divides (nsum(0..n) (\i. 10 EXP i * d(i))) <=>
   3 divides (nsum(0..n) (\i. d i))`;;
