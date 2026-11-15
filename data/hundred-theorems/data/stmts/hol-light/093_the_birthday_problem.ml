(* ========================================================================= *)
(* Birthday problem.                                                         *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Restricted function space.                                                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("-->",(13,"right"));;

let funspace = new_definition
 `(s --> t) = {f:A->B | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> f(x) = @y. T)}`;;

(* ------------------------------------------------------------------------- *)
(* Sizes.                                                                    *)
(* ------------------------------------------------------------------------- *)

let FUNSPACE_EMPTY = `({} --> t) = {(\x. @y. T)}`;;

let HAS_SIZE_FUNSPACE = `!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n ==> (s --> t) HAS_SIZE (n EXP m)`;;

(* ------------------------------------------------------------------------- *)
(* The restriction to injective functions.                                   *)
(* ------------------------------------------------------------------------- *)

let FACT_DIVIDES = `!m n. m <= n ==> ?d. FACT(n) = d * FACT(m)`;;

let FACT_DIV_MULT = `!m n. m <= n ==> FACT n = (FACT(n) DIV FACT(m)) * FACT(m)`;;

let HAS_SIZE_FUNSPACE_INJECTIVE = `!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)}
            HAS_SIZE (if n < m then 0 else (FACT n) DIV (FACT(n - m)))`;;

(* ------------------------------------------------------------------------- *)
(* So the actual birthday result.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_DIFF = `!s t:A->bool m n.
        s SUBSET t /\ s HAS_SIZE m /\ t HAS_SIZE n
        ==> (t DIFF s) HAS_SIZE (n - m)`;;

let BIRTHDAY_THM = `!s:A->bool t:B->bool m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | f IN (s --> t) /\
                 ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
            HAS_SIZE (if m <= n then (n EXP m) - (FACT n) DIV (FACT(n - m))
                      else n EXP m)`;;

(* ------------------------------------------------------------------------- *)
(* The usual explicit instantiation.                                         *)
(* ------------------------------------------------------------------------- *)

let FACT_DIV_SIMP = `!m n. m < n
         ==> (FACT n) DIV (FACT m) = n * FACT(n - 1) DIV FACT(m)`;;

let BIRTHDAY_THM_EXPLICIT = `!s t. s HAS_SIZE 23 /\ t HAS_SIZE 365
         ==> 2 * CARD {f | f IN (s --> t) /\
                           ?x y. x IN s /\ y IN s /\ ~(x = y) /\ f(x) = f(y)}
             >= CARD (s --> t)`;;
