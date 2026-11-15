(* ========================================================================= *)
(* Arithmetic-geometric mean inequality.                                     *)
(* ========================================================================= *)

needs "Library/products.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* There's already one proof of this in "Library/agm.ml". This one is from  *)
(* an article by Michael Hirschhorn, Math. Intelligencer vol. 29, p7.        *)
(* ------------------------------------------------------------------------- *)

let LEMMA_1 = `!x n. x pow (n + 1) - (&n + &1) * x + &n =
         (x - &1) pow 2 * sum(1..n) (\k. &k * x pow (n - k))`;;

let LEMMA_2 = `!n x. &0 <= x ==> &0 <= x pow (n + 1) - (&n + &1) * x + &n`;;

let LEMMA_3 = `!n x. 1 <= n /\ (!i. 1 <= i /\ i <= n + 1 ==> &0 <= x i)
         ==> x(n + 1) * (sum(1..n) x / &n) pow n
                <= (sum(1..n+1) x / (&n + &1)) pow (n + 1)`;;

let AGM = `!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> product(1..n) a <= (sum(1..n) a / &n) pow n`;;

(* ------------------------------------------------------------------------- *)
(* Finally, reformulate in the usual way using roots.                        *)
(* ------------------------------------------------------------------------- *)

needs "Library/transc.ml";;

let AGM_ROOT = `!n a. 1 <= n /\ (!i. 1 <= i /\ i <= n ==> &0 <= a(i))
         ==> root n (product(1..n) a) <= sum(1..n) a / &n`;;
