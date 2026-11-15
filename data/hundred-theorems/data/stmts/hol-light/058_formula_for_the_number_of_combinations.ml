(* ========================================================================= *)
(* Binomial coefficients and relation to number of combinations.             *)
(* ========================================================================= *)

needs "Library/binomial.ml";;

(* ------------------------------------------------------------------------- *)
(* The theorem is really proved in that library file; reformulate it a bit.  *)
(* ------------------------------------------------------------------------- *)

let NUMBER_OF_COMBINATIONS = `!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE binom(n,m)`;;

let NUMBER_OF_COMBINATIONS_EXPLICIT = `!n m s:A->bool.
        s HAS_SIZE n
        ==> {t | t SUBSET s /\ t HAS_SIZE m} HAS_SIZE
            (if n < m then 0 else FACT(n) DIV (FACT(m) * FACT(n - m)))`;;
