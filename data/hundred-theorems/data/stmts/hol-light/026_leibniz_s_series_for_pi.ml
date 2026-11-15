(* ========================================================================= *)
(* #26: Leibniz's series for pi                                              *)
(* ========================================================================= *)

needs "Library/transc.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Summability of alternating series.                                        *)
(* ------------------------------------------------------------------------- *)

let ALTERNATING_SUM_BOUNDS = `!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. (EVEN m ==> &0 <= sum(m,n) a /\ sum(m,n) a <= a(m)) /\
                 (ODD m ==> a(m) <= sum(m,n) a /\ sum(m,n) a <= &0)`;;

let ALTERNATING_SUM_BOUND = `!a. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n)))
       ==> !m n. abs(sum(m,n) a) <= abs(a m)`;;

let SUMMABLE_ALTERNATING = `!v. (!n. a(2 * n + 1) <= &0 /\ &0 <= a(2 * n)) /\
       (!n. abs(a(n + 1)) <= abs(a(n))) /\ a tends_num_real &0
       ==> summable a`;;

(* ------------------------------------------------------------------------- *)
(* Another version of the atan series.                                       *)
(* ------------------------------------------------------------------------- *)

let REAL_ATN_POWSER_ALT = `!x. abs(x) < &1
       ==> (\n. (-- &1) pow n / &(2 * n + 1) * x pow (2 * n + 1))
           sums (atn x)`;;

(* ------------------------------------------------------------------------- *)
(* Summability of the same series for x = 1.                                 *)
(* ------------------------------------------------------------------------- *)

let SUMMABLE_LEIBNIZ = `summable (\n. (-- &1) pow n / &(2 * n + 1))`;;

(* ------------------------------------------------------------------------- *)
(* The tricky sum-bounding lemma.                                            *)
(* ------------------------------------------------------------------------- *)

let SUM_DIFFERENCES = `!a m n. m <= n + 1 ==> sum(m..n) (\i. a(i) - a(i+1)) = a(m) - a(n + 1)`;;

let SUM_REARRANGE_LEMMA = `!a v m n.
        m <= n + 1
        ==> sum(m..n+1) (\i. a i * v i) =
            sum(m..n) (\k. sum(m..k) a * (v(k) - v(k+1))) +
            sum(m..n+1) a * v(n+1)`;;

let SUM_BOUNDS_LEMMA = `!a v l u m n.
        m <= n /\
        (!i. m <= i /\ i <= n ==> &0 <= v(i) /\ v(i+1) <= v(i)) /\
        (!k. m <= k /\ k <= n ==> l <= sum(m..k) a /\ sum(m..k) a <= u)
        ==> l * v(m) <= sum(m..n) (\i. a(i) * v(i)) /\
            sum(m..n) (\i. a(i) * v(i)) <= u * v(m)`;;

let SUM_BOUND_LEMMA = `!a v b m n.
        m <= n /\
        (!i. m <= i /\ i <= n ==> &0 <= v(i) /\ v(i+1) <= v(i)) /\
        (!k. m <= k /\ k <= n ==> abs(sum(m..k) a) <= b)
        ==> abs(sum(m..n) (\i. a(i) * v(i))) <= b * abs(v m)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the final theorem.                                                  *)
(* ------------------------------------------------------------------------- *)

let LEIBNIZ_PI = `(\n. (-- &1) pow n / &(2 * n + 1)) sums (pi / &4)`;;
