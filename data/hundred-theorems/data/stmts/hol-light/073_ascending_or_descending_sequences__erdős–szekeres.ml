(* ========================================================================= *)
(* #73: Erdos-Szekeres theorem on ascending / descending subsequences.       *)
(* ========================================================================= *)

let lemma = `!f s. s = UNIONS (IMAGE (\a. {x | x IN s /\ f(x) = a}) (IMAGE f s))`;;

(* ------------------------------------------------------------------------- *)
(* Pigeonhole lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let PIGEONHOLE_LEMMA = `!f:A->B s n.
        FINITE s /\ (n - 1) * CARD(IMAGE f s) < CARD s
        ==> ?t a. t SUBSET s /\ t HAS_SIZE n /\ (!x. x IN t ==> f(x) = a)`;;

(* ------------------------------------------------------------------------- *)
(* Abbreviation for "monotonicity of f on s w.r.t. ordering r".              *)
(* ------------------------------------------------------------------------- *)

let mono_on = define
 `mono_on (f:num->real) r s <=>
    !i j. i IN s /\ j IN s /\ i <= j ==> r (f i) (f j)`;;

let MONO_ON_SUBSET = `!s t. t SUBSET s /\ mono_on f r s ==> mono_on f r t`;;

(* ------------------------------------------------------------------------- *)
(* The main result.                                                          *)
(* ------------------------------------------------------------------------- *)

let ERDOS_SZEKERES = `!f:num->real m n.
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (m + 1) /\ mono_on f (<=) s) \/
        (?s. s SUBSET (1..m*n+1) /\ s HAS_SIZE (n + 1) /\ mono_on f (>=) s)`;;
