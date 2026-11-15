(* ========================================================================= *)
(* Independence of the parallel postulate. The statement and some ideas are  *)
(* taken from Tim Makarios's MSc thesis "A mechanical verification of the    *)
(* independence of Tarski's Euclidean axiom".                                *)
(*                                                                           *)
(* In the file Multivariate/tarski.ml it is shown that all 11 of Tarski's    *)
(* axioms for geometry hold for the Euclidean plane `:real^2`, with          *)
(* betweenness and congruence of segments as:                                *)
(*                                                                           *)
(*      B x y z  <=> between y (x,z)                                         *)
(*      ab == pq <=> dist(a,b) = dist(p,q)                                   *)
(*                                                                           *)
(* The present file shows that the Klein model of the hyperbolic plane (type *)
(* `:plane`) satisfies all Tarski's axioms except that it satisfies the      *)
(* negation of the Euclidean axiom (10), with betweenness and congruence of  *)
(* segments as:                                                              *)
(*                                                                           *)
(*      B x y z  <=> pbetween y (x,z)                                        *)
(*      ab == pq <=> pdist(a,b) = pdist(p,q)                                 *)
(*                                                                           *)
(* Collectively, these two results show that the Euclidean axiom is          *)
(* independent of the others. For more references regarding Tarski's axioms  *)
(* for geometry see "http://en.wikipedia.org/wiki/Tarski's_axioms".          *)
(* ========================================================================= *)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/tarski.ml";;

(* ------------------------------------------------------------------------- *)
(* The semimetric we will use, directly on real^N first. Choose a sensible   *)
(* default outside unit ball so some handy theorems become unconditional.    *)
(* ------------------------------------------------------------------------- *)

let ddist = new_definition
 `ddist(x:real^N,y:real^N) =
    if norm(x) < &1 /\ norm(y) < &1 then
     (&1 - x dot y) pow 2 / ((&1 - norm(x) pow 2) * (&1 - norm(y) pow 2)) - &1
    else dist(x,y)`;;

let DDIST_INCREASES_ONLINE = `!a b x:real^N.
      norm a < &1 /\ norm b < &1 /\ norm x < &1 /\ between x (a,b) /\ ~(x = b)
      ==> ddist(a,x) < ddist(a,b)`;;

let DDIST_REFL = `!x:real^N. ddist(x,x) = &0`;;

let DDIST_SYM = `!x y:real^N. ddist(x,y) = ddist(y,x)`;;

let DDIST_POS_LT = `!x y:real^N. ~(x = y) ==> &0 < ddist(x,y)`;;

let DDIST_POS_LE = `!x y:real^N. &0 <= ddist(x,y)`;;

let DDIST_EQ_0 = `!x y:real^N. ddist(x,y) = &0 <=> x = y`;;

let BETWEEN_COLLINEAR_DDIST_EQ = `!a b x:real^N.
        norm(a) < &1 /\ norm(b) < &1 /\ norm(x) < &1
        ==> (between x (a,b) <=>
             collinear {a, x, b} /\
             ddist(x,a) <= ddist (a,b) /\ ddist(x,b) <= ddist(a,b))`;;

let CONTINUOUS_AT_LIFT_DDIST = `!a x:real^N.
      norm(a) < &1 /\ norm(x) < &1 ==> (\x. lift(ddist(a,x))) continuous at x`;;

let HYPERBOLIC_MIDPOINT = `!a b:real^N.
        norm a < &1 /\ norm b < &1
        ==> ?x. between x (a,b) /\ ddist(x,a) = ddist(x,b)`;;

let DDIST_EQ_ORIGIN = `!x:real^N y:real^N.
        norm x < &1 /\ norm y < &1
        ==> (ddist(vec 0,x) = ddist(vec 0,y) <=> norm x = norm y)`;;

let DDIST_CONGRUENT_TRIPLES_0 = `!a b:real^N a' b':real^N.
        norm a < &1 /\ norm b < &1 /\ norm a' < &1 /\ norm b' < &1
        ==> (ddist(vec 0,a) = ddist(vec 0,a') /\ ddist(a,b) = ddist(a',b') /\
             ddist(b,vec 0) = ddist(b',vec 0) <=>
             dist(vec 0,a) = dist(vec 0,a') /\ dist(a,b) = dist(a',b') /\
             dist(b,vec 0) = dist(b',vec 0))`;;

(* ------------------------------------------------------------------------- *)
(* Deduce existence of hyperbolic translations via the Poincare disc model.  *)
(* Use orthogonal projection onto a hemisphere touching the unit disc,       *)
(* then stereographic projection back from the other pole of the sphere plus *)
(* scaling. See Greenberg's "Euclidean & Non-Euclidean Geometries" fig 7.13. *)
(* ------------------------------------------------------------------------- *)

let kleinify = new_definition
 `kleinify z = Cx(&2 / (&1 + norm(z) pow 2)) * z`;;

let poincarify = new_definition
 `poincarify x = Cx((&1 - sqrt(&1 - norm(x) pow 2)) / norm(x) pow 2) * x`;;

let KLEINIFY_0,POINCARIFY_0 = (CONJ_PAIR o prove)
 (`kleinify (Cx(&0)) = Cx(&0) /\ poincarify (Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[kleinify; poincarify; COMPLEX_MUL_RZERO]);;

let NORM_KLEINIFY = `!z. norm(kleinify z) = (&2 * norm(z)) / (&1 + norm(z) pow 2)`;;

let NORM_KLEINIFY_LT = `!z. norm(kleinify z) < &1 <=> ~(norm z = &1)`;;

let NORM_POINCARIFY_LT = `!x. norm(x) < &1 ==> norm(poincarify x) < &1`;;

let KLEINIFY_POINCARIFY = `!x. norm(x) < &1 ==> kleinify(poincarify x) = x`;;

let POINCARIFY_KLEINIFY = `!x. norm(x) < &1 ==> poincarify(kleinify x) = x`;;

let DDIST_KLEINIFY = `!w z. ~(norm w = &1) /\ ~(norm z = &1)
         ==> ddist(kleinify w,kleinify z) =
             &4 * (&1 / &2 + norm(w - z) pow 2 /
                             ((&1 - norm w pow 2) * (&1 - norm z pow 2))) pow 2
             - &1`;;

let DDIST_KLEINIFY_EQ = `!w z w' z'.
      ~(norm w = &1) /\ ~(norm z = &1) /\ ~(norm w' = &1) /\ ~(norm z' = &1) /\
      norm(w - z) pow 2 * (&1 - norm w' pow 2) * (&1 - norm z' pow 2) =
      norm(w' - z') pow 2 * (&1 - norm w pow 2) * (&1 - norm z pow 2)
      ==> ddist(kleinify w,kleinify z) = ddist(kleinify w',kleinify z')`;;

let NORM_KLEINIFY_MOEBIUS_LT = `!w x. norm w < &1 /\ norm x < &1
         ==> norm(kleinify(moebius_function (&0) w x)) < &1`;;

let DDIST_KLEINIFY_MOEBIUS = `!w x y. norm w < &1 /\ norm x < &1 /\ norm y < &1
           ==> ddist(kleinify(moebius_function (&0) w x),
                     kleinify(moebius_function (&0) w y)) =
               ddist(kleinify x,kleinify y)`;;

let COLLINEAR_KLEINIFY_MOEBIUS = `!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (collinear {kleinify(moebius_function (&0) w x),
                             kleinify(moebius_function (&0) w y),
                             kleinify(moebius_function (&0) w z)} <=>
                  collinear {kleinify x,kleinify y,kleinify z})`;;

let BETWEEN_KLEINIFY_MOEBIUS = `!w x y z. norm w < &1 /\ norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (kleinify(moebius_function (&0) w x))
                          (kleinify(moebius_function (&0) w y),
                           kleinify(moebius_function (&0) w z)) <=>
                  between (kleinify x) (kleinify y,kleinify z))`;;

let hyperbolic_isometry = new_definition
 `hyperbolic_isometry (f:real^2->real^2) <=>
    (!x. norm x < &1 ==> norm(f x) < &1) /\
    (!x y. norm x < &1 /\ norm y < &1 ==> ddist(f x,f y) = ddist(x,y)) /\
    (!x y z. norm x < &1 /\ norm y < &1 /\ norm z < &1
             ==> (between (f x) (f y,f z) <=> between x (y,z)))`;;

let HYPERBOLIC_TRANSLATION = `!w. norm w < &1
       ==> ?f:real^2->real^2 g:real^2->real^2.
                hyperbolic_isometry f /\ hyperbolic_isometry g /\
                f(w) = vec 0 /\ g(vec 0) = w /\
                (!x. norm x < &1 ==> f(g x) = x) /\
                (!x. norm x < &1 ==> g(f x) = x)`;;

(* ------------------------------------------------------------------------- *)
(* Our model.                                                                *)
(* ------------------------------------------------------------------------- *)

let plane_tybij =
  let th = prove
   (`?x:real^2. norm x < &1`,
    EXISTS_TAC `vec 0:real^2` THEN NORM_ARITH_TAC) in
  new_type_definition "plane" ("mk_plane","dest_plane") th;;

let pbetween = new_definition
 `pbetween y (x,z) <=> between (dest_plane y) (dest_plane x,dest_plane z)`;;

let pdist = new_definition
 `pdist(x,y) = ddist(dest_plane x,dest_plane y)`;;

let DEST_PLANE_EQ = `!x y. dest_plane x = dest_plane y <=> x = y`;;

let FORALL_DEST_PLANE = `!P. (!x. P(dest_plane x)) <=> (!x. norm x < &1 ==> P x)`;;

let EXISTS_DEST_PLANE = `!P. (?x. P(dest_plane x)) <=> (?x. norm x < &1 /\ P x)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 1 (reflexivity for equidistance).                                   *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_1_NONEUCLIDEAN = `!a b. pdist(a,b) = pdist(b,a)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 2 (transitivity for equidistance).                                  *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_2_NONEUCLIDEAN = `!a b p q r s.
        pdist(a,b) = pdist(p,q) /\ pdist(a,b) = pdist(r,s)
        ==> pdist(p,q) = pdist(r,s)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 3 (identity for equidistance).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_3_NONEUCLIDEAN = `!a b c. pdist(a,b) = pdist(c,c) ==> a = b`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 4 (segment construction).                                           *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_4_NONEUCLIDEAN = `!a q b c. ?x. pbetween a (q,x) /\ pdist(a,x) = pdist(b,c)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 5 (five-segments axiom).                                            *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_5_NONEUCLIDEAN = `!a b c x a' b' c' x'.
        ~(a = b) /\
        pdist(a,b) = pdist(a',b') /\
        pdist(a,c) = pdist(a',c') /\
        pdist(b,c) = pdist(b',c') /\
        pbetween b (a,x) /\ pbetween b' (a',x') /\ pdist(b,x) = pdist(b',x')
        ==> pdist(c,x) = pdist(c',x')`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 6 (identity for between-ness).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_6_NONEUCLIDEAN = `!a b. pbetween b (a,a) ==> a = b`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 7 (Pasch's axiom).                                                  *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_7_NONEUCLIDEAN = `!a b c p q.
    pbetween p (a,c) /\ pbetween q (b,c)
    ==> ?x. pbetween x (p,b) /\ pbetween x (q,a)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 8 (lower 2-dimensional axiom).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_8_NONEUCLIDEAN = `?a b c. ~pbetween b (a,c) /\ ~pbetween c (b,a) /\ ~pbetween a (c,b)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 9 (upper 2-dimensional axiom).                                      *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_9_NONEUCLIDEAN = `!p q a b c.
        ~(p = q) /\
        pdist(a,p) = pdist(a,q) /\ pdist(b,p) = pdist(b,q) /\
        pdist(c,p) = pdist(c,q)
        ==> pbetween b (a,c) \/ pbetween c (b,a) \/ pbetween a (c,b)`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 10 (Euclidean axiom).                                               *)
(* ------------------------------------------------------------------------- *)

let NOT_TARSKI_AXIOM_10_NONEUCLIDEAN = `~(!a b c d t.
      pbetween d (a,t) /\ pbetween d (b,c) /\ ~(a = d)
      ==> ?x y. pbetween b (a,x) /\ pbetween c (a,y) /\ pbetween t (x,y))`;;

(* ------------------------------------------------------------------------- *)
(* Axiom 11 (Continuity).                                                    *)
(* ------------------------------------------------------------------------- *)

let TARSKI_AXIOM_11_NONEUCLIDEAN = `!X Y. (?a. !x y. x IN X /\ y IN Y ==> pbetween x (a,y))
         ==> (?b. !x y. x IN X /\ y IN Y ==> pbetween b (x,y))`;;
