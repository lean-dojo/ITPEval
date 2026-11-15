(* ========================================================================= *)
(* Minkowski's convex body theorem.                                          *)
(* ========================================================================= *)

needs "Multivariate/measure.ml";;

(* ------------------------------------------------------------------------- *)
(* An ad hoc lemma.                                                          *)
(* ------------------------------------------------------------------------- *)

let LEMMA = `!f:real^N->bool t s:real^N->bool.
        FINITE { u | u IN f /\ ~(t u = {})} /\
        measurable s /\ &1 < measure s /\
        (!u. u IN f ==> measurable(t u)) /\
        s SUBSET UNIONS (IMAGE t f) /\
        (!u v. u IN f /\ v IN f /\ ~(u = v) ==> DISJOINT (t u) (t v)) /\
        (!u. u IN f ==> (IMAGE (\x. x - u) (t u)) SUBSET interval[vec 0,vec 1])
        ==> ?u v. u IN f /\ v IN f /\ ~(u = v) /\
                  ~(DISJOINT (IMAGE (\x. x - u) (t u))
                             (IMAGE (\x. x - v) (t v)))`;;

(* ------------------------------------------------------------------------- *)
(* This is also interesting, and Minkowski follows easily from it.           *)
(* ------------------------------------------------------------------------- *)

let BLICHFELDT = `!s:real^N->bool.
        measurable s /\ &1 < measure s
        ==> ?x y. x IN s /\ y IN s /\ ~(x = y) /\
                  !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i - y$i)`;;

(* ------------------------------------------------------------------------- *)
(* The usual form of the theorem.                                            *)
(* ------------------------------------------------------------------------- *)

let MINKOWSKI = `!s:real^N->bool.
        convex s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) < measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`;;

(* ------------------------------------------------------------------------- *)
(* A slightly sharper variant for use when the set is also closed.           *)
(* ------------------------------------------------------------------------- *)

let MINKOWSKI_COMPACT = `!s:real^N->bool.
        convex s /\ compact s /\
        (!x. x IN s ==> (--x) IN s) /\
        &2 pow dimindex(:N) <= measure s
        ==> ?u. ~(u = vec 0) /\
                (!i. 1 <= i /\ i <= dimindex(:N) ==> integer(u$i)) /\
                u IN s`;;
