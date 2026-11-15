(* ========================================================================= *)
(* Euclidean GCD algorithm.                                                  *)
(* ========================================================================= *)

needs "Library/prime.ml";;

let egcd = define
 `egcd(m,n) = if m = 0 then n
              else if n = 0 then m
              else if m <= n then egcd(m,n - m)
              else egcd(m - n,n)`;;

(* ------------------------------------------------------------------------- *)
(* Main theorems.                                                            *)
(* ------------------------------------------------------------------------- *)

let EGCD_INVARIANT = `!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n`;;

(* ------------------------------------------------------------------------- *)
(* Hence we get the proper behaviour, and it's equal to the real GCD.        *)
(* ------------------------------------------------------------------------- *)

let EGCD_GCD = `!m n. egcd(m,n) = gcd(m,n)`;;

let EGCD = `!a b. (egcd (a,b) divides a /\ egcd (a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides egcd (a,b))`;;
