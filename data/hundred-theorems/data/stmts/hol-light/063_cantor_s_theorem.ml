(* ========================================================================= *)
(* Cantor's theorem.                                                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Ad hoc version for whole type.                                            *)
(* ------------------------------------------------------------------------- *)

let CANTOR_THM_INJ = `~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`;;

let CANTOR_THM_SURJ = `~(?f:A->(A->bool). !s. ?x. f x = s)`;;

(* ------------------------------------------------------------------------- *)
(* Proper version for any set, in terms of cardinality operators.            *)
(* ------------------------------------------------------------------------- *)

let CANTOR = `!s:A->bool. s <_c {t | t SUBSET s}`;;

(* ------------------------------------------------------------------------- *)
(* More explicit "injective" version as in Paul Taylor's book.               *)
(* ------------------------------------------------------------------------- *)

let CANTOR_THM_INJ' = `~(?f:(A->bool)->A. (!x y. f(x) = f(y) ==> x = y))`;;

(* ------------------------------------------------------------------------- *)
(* Another sequence of versions (Lawvere, Cantor, Taylor) taken from         *)
(* http://ncatlab.org/nlab/show/Cantor%27s+theorem.                          *)
(* ------------------------------------------------------------------------- *)

let CANTOR_LAWVERE = `!h:A->(A->B).
        (!f:A->B. ?x:A. h(x) = f) ==> !n:B->B. ?x. n(x) = x`;;

let CANTOR = `!f:A->(A->bool). ~(!s. ?x. f x = s)`;;

let CANTOR_TAYLOR = `!f:(A->bool)->A. ~(!x y. f(x) = f(y) ==> x = y)`;;

let SURJECTIVE_COMPOSE = `(!y. ?x. f(x) = y) /\ (!z. ?y. g(y) = z)
   ==> (!z. ?x. (g o f) x = z)`;;

let INJECTIVE_SURJECTIVE_PREIMAGE = `!f:A->B. (!x y. f(x) = f(y) ==> x = y) ==> !t. ?s. {x | f(x) IN s} = t`;;

let CANTOR_JOHNSTONE = `!i:B->S f:B->S->bool.
        ~((!x y. i(x) = i(y) ==> x = y) /\ (!s. ?z. f(z) = s))`;;
