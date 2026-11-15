(* ========================================================================= *)
(* Sum of an arithmetic series.                                              *)
(* ========================================================================= *)

let ARITHMETIC_PROGRESSION_LEMMA = `!n. nsum(0..n) (\i. a + d * i) = ((n + 1) * (2 * a + n * d)) DIV 2`;;

let ARITHMETIC_PROGRESSION = `!n. 1 <= n
       ==> nsum(0..n-1) (\i. a + d * i) = (n * (2 * a + (n - 1) * d)) DIV 2`;;
