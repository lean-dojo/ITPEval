(* ========================================================================= *)
(* Transfer of homological definition of Brouwer degree to our Multivariate  *)
(* context, used to get some key results about homotopy of linear mappings   *)
(* and so all the usual things like Brouwer's fixed-point theorem.           *)
(*                                                                           *)
(*                 (c) Copyright, John Harrison 2017-2018                    *)
(* ========================================================================= *)

needs "Multivariate/homology.ml";;
needs "Multivariate/polytope.ml";;

(* ------------------------------------------------------------------------- *)
(* Transfer of Brouwer degree from product topology setting.                 *)
(* ------------------------------------------------------------------------- *)

let brouwer_degree1 = new_definition
 `brouwer_degree1 n (f:real^N->real^N) =
        if 1 <= n /\ n <= dimindex(:N)
        then brouwer_degree2 (n - 1)
              ((\x i. if 1 <= i /\ i <= n then x$i else &0) o
               f o
               (\x. lambda i. if 1 <= i /\ i <= n then x i else &0))
        else &1`;;

let brouwer_degree = new_definition
 `brouwer_degree (f:real^N->real^N) = brouwer_degree1 (dimindex(:N)) f`;;

let BROUWER_DEGREE1_EQ = `!n f g:real^N->real^N.
        (!x. x IN sphere(vec 0,&1) INTER span(IMAGE basis (1..n))
             ==> f x = g x)
        ==> brouwer_degree1 n f = brouwer_degree1 n g`;;

let BROUWER_DEGREE1_ID = `!n. brouwer_degree1 n (\x:real^N. x) = &1`;;

let BROUWER_DEGREE1_COMPOSE = `!n f g:real^N->real^N.
        f continuous_on (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        g continuous_on (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        IMAGE f (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) SUBSET
                (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        IMAGE g (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) SUBSET
                (sphere(vec 0,&1) INTER span(IMAGE basis (1..n)))
        ==> brouwer_degree1 n (g o f) =
            brouwer_degree1 n g * brouwer_degree1 n f`;;

let BROUWER_DEGREE1_HOMOTOPIC = `!n f g:real^N->real^N.
     homotopic_with (\x. T)
      (subtopology euclidean (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))),
       subtopology euclidean (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))))
      f g
     ==> brouwer_degree1 n f = brouwer_degree1 n g`;;

let BROUWER_DEGREE1_CONST = `!n a:real^N.
      1 <= n /\ n <= dimindex(:N) ==> brouwer_degree1 n (\x. a) = &0`;;

let BROUWER_DEGREE1_REFLECT_ALONG = `!n a:real^N.
        1 <= n /\ n <= dimindex(:N) /\
        a IN span(IMAGE basis (1..n)) DELETE vec 0
        ==> brouwer_degree1 n (reflect_along a) = -- &1`;;

let BROUWER_DEGREE1_NONSURJECTIVE = `!n (f:real^N->real^N).
        1 <= n /\ n <= dimindex(:N) /\
        f continuous_on (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) /\
        IMAGE f (sphere(vec 0,&1) INTER span(IMAGE basis (1..n))) PSUBSET
                (sphere(vec 0,&1) INTER span(IMAGE basis (1..n)))
        ==> brouwer_degree1 n f = &0`;;

let BROUWER_DEGREE_EQ = `!f g:real^N->real^N.
        (!x. x IN sphere(vec 0,&1) ==> f x = g x)
        ==> brouwer_degree f = brouwer_degree g`;;

let BROUWER_DEGREE_ID = `brouwer_degree (\x:real^N. x) = &1`;;

let BROUWER_DEGREE_COMPOSE = `!f g:real^N->real^N.
        f continuous_on sphere(vec 0,&1) /\
        g continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1) /\
        IMAGE g (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1)
        ==> brouwer_degree (g o f) = brouwer_degree g * brouwer_degree f`;;

let BROUWER_DEGREE_HOMOTOPIC = `!f g:real^N->real^N.
     homotopic_with (\x. T)
      (subtopology euclidean (sphere(vec 0,&1)),
       subtopology euclidean (sphere(vec 0,&1)))
      f g
     ==> brouwer_degree f = brouwer_degree g`;;

let BROUWER_DEGREE_CONST = `!a:real^N. brouwer_degree (\x. a) = &0`;;

let BROUWER_DEGREE_REFLECT_ALONG = `!a:real^N. ~(a = vec 0) ==> brouwer_degree (reflect_along a) = -- &1`;;

let BROUWER_DEGREE_NONSURJECTIVE = `!(f:real^N->real^N).
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) PSUBSET sphere(vec 0,&1)
        ==> brouwer_degree f = &0`;;

let BROUWER_DEGREE_ORTHOGONAL_TRANSFORMATION = `!(f:real^N->real^N).
        orthogonal_transformation f
        ==> real_of_int(brouwer_degree f) = det(matrix f)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the key theorem about homotopy of linear maps.                      *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS = `!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g
        ==> (homotopic_with (\x. T)
              (subtopology euclidean (sphere (vec 0,&1)),
               subtopology euclidean (sphere (vec 0,&1))) f g <=>
             det(matrix f) = det(matrix g))`;;

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_ALT = `!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g
        ==> (homotopic_with (\x. T)
              (subtopology euclidean ((:real^N) DELETE vec 0),
               subtopology euclidean ((:real^N) DELETE vec 0))
              f g <=>
             det(matrix f) = det(matrix g))`;;

let HOMOTOPIC_ORTHOGONAL_TRANSFORMATIONS_IMP = `!f g:real^N->real^N.
        orthogonal_transformation f /\ orthogonal_transformation g /\
        homotopic_with (\x. T)
          (subtopology euclidean (sphere (vec 0,&1)),
           subtopology euclidean (sphere (vec 0,&1))) f g
        ==> det(matrix f) = det(matrix g)`;;

let HOMOTOPIC_LINEAR_MAPS_IMP = `!f g:real^N->real^N.
     linear f /\ linear g /\
     homotopic_with (\x. T)
       (subtopology euclidean ((:real^N) DELETE vec 0),
        subtopology euclidean ((:real^N) DELETE vec 0)) f g
     ==> real_sgn(det(matrix f)) = real_sgn(det(matrix g))`;;

let HOMOTOPIC_LINEAR_MAPS_ALT = `!f g:real^N->real^N.
     linear f /\ linear g /\
     homotopic_with (\x. T)
        (subtopology euclidean ((:real^N) DELETE vec 0),
         subtopology euclidean ((:real^N) DELETE vec 0)) f g
     ==> &0 < det(matrix f) * det(matrix g)`;;

(* ------------------------------------------------------------------------- *)
(* Hairy ball theorem and relatives.                                         *)
(* ------------------------------------------------------------------------- *)

let FIXPOINT_HOMOTOPIC_IDENTITY_SPHERE = `!f:real^N->real^N.
        ODD(dimindex(:N)) /\
        homotopic_with (\x. T)
         (subtopology euclidean (sphere(vec 0,&1)),
          subtopology euclidean (sphere(vec 0,&1))) (\x. x) f
        ==> ?x. x IN sphere(vec 0,&1) /\ f x = x`;;

let FIXPOINT_OR_NEG_MAPPING_SPHERE = `!f:real^N->real^N.
        ODD(dimindex(:N)) /\
        f continuous_on sphere(vec 0,&1) /\
        IMAGE f (sphere(vec 0,&1)) SUBSET sphere(vec 0,&1)
        ==> ?x. x IN sphere(vec 0,&1) /\ (f x = --x \/ f x = x)`;;

let HAIRY_BALL_THEOREM_ALT,HAIRY_BALL_THEOREM = (CONJ_PAIR o prove)
 (`(!r. (?f. f continuous_on sphere(vec 0:real^N,r) /\
             (!x. x IN sphere(vec 0,r)
                  ==> ~(f x = vec 0) /\ orthogonal x (f x))) <=>
        r <= &0 \/ EVEN(dimindex(:N))) /\
   (!r. (?f. f continuous_on sphere(vec 0:real^N,r) /\
             IMAGE f (sphere(vec 0,r)) SUBSET sphere(vec 0,r) /\
             (!x. x IN sphere(vec 0,r)
                  ==> ~(f x = vec 0) /\ orthogonal x (f x))) <=>
        r < &0 \/ &0 < r /\ EVEN(dimindex(:N)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `r:real` THEN
  ASM_CASES_TAC `r < &0` THEN
  ASM_SIMP_TAC[SPHERE_EMPTY; NOT_IN_EMPTY; IMAGE_CLAUSES; EMPTY_SUBSET;
               CONTINUOUS_ON_EMPTY; REAL_LT_IMP_LE] THEN
  ASM_CASES_TAC `r = &0` THEN ASM_REWRITE_TAC[REAL_LE_REFL; REAL_LT_REFL] THENL
   [SIMP_TAC[SPHERE_SING; FORALL_IN_INSERT; NOT_IN_EMPTY; SUBSET;
             FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL [ALL_TAC; MESON_TAC[IN_SING]] THEN
    EXISTS_TAC `(\x. basis 1):real^N->real^N` THEN
    SIMP_TAC[CONTINUOUS_ON_CONST; ORTHOGONAL_0; BASIS_NONZERO; LE_REFL;
             DIMINDEX_GE_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[GSYM REAL_NOT_LT]] THEN
  MATCH_MP_TAC(TAUT
   `(q ==> p) /\ (p ==> r) /\ (r ==> q)
    ==> (p <=> r) /\ (q <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
    REWRITE_TAC[GSYM NOT_ODD] THEN REPEAT STRIP_TAC THEN
    MP_TAC(SPEC `\x. inv(norm(f(r % x))) % (f:real^N->real^N) (r % x)`
          FIXPOINT_OR_NEG_MAPPING_SPHERE) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF] THEN
        MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE;
          X_GEN_TAC `x:real^N` THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `r % x:real^N`) THEN
          ASM_SIMP_TAC[NORM_MUL; real_abs; REAL_LT_IMP_LE; NORM_EQ_0;
                       IN_SPHERE_0; REAL_MUL_RID]];
        ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_SIMP_TAC[GSYM SPHERE_SCALING; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID;
                   VECTOR_MUL_RZERO; REAL_MUL_RID];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN
      ASM_SIMP_TAC[NORM_MUL; real_abs; REAL_LT_IMP_LE; NORM_EQ_0;
                   IN_SPHERE_0; REAL_MUL_RID];
      REWRITE_TAC[IN_SPHERE_0; VECTOR_ARITH `a:real^N = --x <=> --a = x`] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r % x:real^N`) THEN
      ASM_SIMP_TAC[NORM_MUL; real_abs; REAL_LT_IMP_LE; NORM_EQ_0;
                   IN_SPHERE_0; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[ORTHOGONAL_MUL; REAL_LT_IMP_NZ] THEN
      FIRST_X_ASSUM(fun th ->
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
      REWRITE_TAC[ORTHOGONAL_MUL; ORTHOGONAL_LNEG; ORTHOGONAL_REFL;
                  REAL_INV_EQ_0; NORM_EQ_0] THEN
      CONV_TAC TAUT];
    REWRITE_TAC[EVEN_EXISTS] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `(\x. lambda i. if EVEN(i) then --(x$(i-1)) else x$(i+1)):
                real^N->real^N` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
      SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               LAMBDA_BETA; REAL_NEG_ADD; GSYM REAL_MUL_RNEG] THEN
      MESON_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; GSYM DOT_EQ_0] THEN
      SIMP_TAC[orthogonal; dot; LAMBDA_BETA; NORM_EQ_SQUARE]] THEN
    SUBGOAL_THEN `1..dimindex(:N) = 2*0+1..(2 * (n - 1) + 1) + 1`
    SUBST1_TAC THENL
     [BINOP_TAC THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ARITH_RULE
        `m = 2 * n ==> 1 <= m ==> m = (2 * (n - 1) + 1) + 1`)) THEN
      REWRITE_TAC[DIMINDEX_GE_1];
      REWRITE_TAC[SUM_OFFSET; SUM_PAIR]] THEN
    REWRITE_TAC[EVEN_ADD; EVEN_MULT; ARITH; ADD_SUB] THEN
    REWRITE_TAC[REAL_ARITH `a + --x * --y:real = x * y + a`] THEN
    ASM_SIMP_TAC[REAL_POW_EQ_0; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[REAL_ARITH `x + y * --z = x - z * y`; REAL_SUB_REFL; SUM_0]]);;

let CONTINUOUS_FUNCTION_HAS_EIGENVALUES_ODD_DIM = `!f:real^N->real^N.
        ODD(dimindex(:N)) /\ f continuous_on sphere(vec 0:real^N,&1)
        ==> ?v c. v IN sphere(vec 0,&1) /\ f v = c % v`;;

let EULER_ROTATION_THEOREM_GEN = `!A:real^N^N.
        ODD(dimindex(:N)) /\ rotation_matrix A
        ==> ?v. norm v = &1 /\ A ** v = v`;;

(* ------------------------------------------------------------------------- *)
(* Retractions.                                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("retract_of",(12,"right"));;

let retraction = new_definition
  `retraction (s,t) (r:real^N->real^N) <=>
        t SUBSET s /\ r continuous_on s /\ (IMAGE r s SUBSET t) /\
        (!x. x IN t ==> (r x = x))`;;

let retract_of = new_definition
  `t retract_of s <=> ?r. retraction (s,t) r`;;

let RETRACTION_MAPS_EUCLIDEAN = `!r s t:real^N->bool.
        retraction_maps (subtopology euclidean s,subtopology euclidean t)
                        (r,I) <=>
   retraction (s,t) r`;;

let RETRACT_OF_SPACE_EUCLIDEAN = `!s t:real^N->bool.
        t retract_of_space (subtopology euclidean s) <=> t retract_of s`;;

let RETRACTION = `!s t r. retraction (s,t) r <=>
           t SUBSET s /\
           r continuous_on s /\
           IMAGE r s = t /\
           (!x. x IN t ==> r x = x)`;;

let RETRACT_OF_IMP_EXTENSIBLE = `!f:real^M->real^N u s t.
        s retract_of t /\ f continuous_on s /\ IMAGE f s SUBSET u
        ==> ?g. g continuous_on t /\ IMAGE g t SUBSET u /\
                (!x. x IN s ==> g x = f x)`;;

let RETRACTION_IDEMPOTENT = `!r s t. retraction (s,t) r ==> !x. x IN s ==> (r(r(x)) = r(x))`;;

let IDEMPOTENT_IMP_RETRACTION = `!f:real^N->real^N s.
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (!x. x IN s ==> f(f x) = f x)
        ==> retraction (s,IMAGE f s) f`;;

let RETRACTION_SUBSET = `!r s s' t. retraction (s,t) r /\ t SUBSET s' /\ s' SUBSET s
              ==> retraction (s',t) r`;;

let RETRACT_OF_SUBSET = `!s s' t. t retract_of s /\ t SUBSET s' /\ s' SUBSET s
            ==> t retract_of s'`;;

let RETRACT_OF_TRANSLATION = `!a t s:real^N->bool.
        t retract_of s
        ==> (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s)`;;

let RETRACT_OF_TRANSLATION_EQ = `!a t s:real^N->bool.
        (IMAGE (\x. a + x) t) retract_of (IMAGE (\x. a + x) s) <=>
        t retract_of s`;;

add_translation_invariants [RETRACT_OF_TRANSLATION_EQ];;

let RETRACT_OF_INJECTIVE_LINEAR_IMAGE = `!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ t retract_of s
        ==> (IMAGE f t) retract_of (IMAGE f s)`;;

let RETRACT_OF_LINEAR_IMAGE_EQ = `!f:real^M->real^N s t.
        linear f /\ (!x y. f x = f y ==> x = y) /\ (!y. ?x. f x = y)
        ==> ((IMAGE f t) retract_of (IMAGE f s) <=> t retract_of s)`;;

add_linear_invariants [RETRACT_OF_LINEAR_IMAGE_EQ];;

let RETRACTION_REFL = `!s. retraction (s,s) (\x. x)`;;

let RETRACT_OF_REFL = `!s. s retract_of s`;;

let RETRACTION_CLOSEST_POINT = `!s t:real^N->bool.
        convex t /\ closed t /\ ~(t = {}) /\ t SUBSET s
        ==> retraction (s,t) (closest_point t)`;;

let RETRACT_OF_IMP_SUBSET = `!s t. s retract_of t ==> s SUBSET t`;;

let RETRACT_OF_EMPTY = `(!s:real^N->bool. {} retract_of s <=> s = {}) /\
   (!s:real^N->bool. s retract_of {} <=> s = {})`;;

let RETRACT_OF_SING = `!s x:real^N. {x} retract_of s <=> x IN s`;;

let RETRACT_OF_OPEN_UNION = `!s t:real^N->bool.
        open_in (subtopology euclidean (s UNION t)) s /\
        open_in (subtopology euclidean (s UNION t)) t /\
        DISJOINT s t /\ (s = {} ==> t = {})
        ==> s retract_of (s UNION t)`;;

let RETRACT_OF_SEPARATED_UNION = `!s t:real^N->bool.
        s INTER closure t = {} /\ t INTER closure s = {} /\
        (s = {} ==> t = {})
        ==> s retract_of (s UNION t)`;;

let RETRACT_OF_CLOSED_UNION = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        DISJOINT s t /\ (s = {} ==> t = {})
        ==> s retract_of (s UNION t)`;;

let RETRACTION_o = `!f g s t u:real^N->bool.
        retraction (s,t) f /\ retraction (t,u) g
        ==> retraction (s,u) (g o f)`;;

let RETRACT_OF_TRANS = `!s t u:real^N->bool.
        s retract_of t /\ t retract_of u ==> s retract_of u`;;

let CLOSED_IN_RETRACT = `!s t:real^N->bool.
        s retract_of t ==> closed_in (subtopology euclidean t) s`;;

let RETRACT_OF_CONTRACTIBLE = `!s t:real^N->bool. contractible t /\ s retract_of t ==> contractible s`;;

let RETRACT_OF_COMPACT = `!s t:real^N->bool. compact t /\ s retract_of t ==> compact s`;;

let RETRACT_OF_CLOSED = `!s t. closed t /\ s retract_of t ==> closed s`;;

let RETRACT_OF_CONNECTED = `!s t:real^N->bool. connected t /\ s retract_of t ==> connected s`;;

let RETRACT_OF_PATH_CONNECTED = `!s t:real^N->bool. path_connected t /\ s retract_of t ==> path_connected s`;;

let RETRACT_OF_SIMPLY_CONNECTED = `!s t:real^N->bool.
       simply_connected t /\ s retract_of t ==> simply_connected s`;;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL = `!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on u /\ IMAGE f u SUBSET s /\
               g continuous_on u /\ IMAGE g u SUBSET s
               ==> homotopic_with (\x. T)
                     (subtopology euclidean u,subtopology euclidean s)  f g)
        ==> (!f g. f continuous_on u /\ IMAGE f u SUBSET t /\
                   g continuous_on u /\ IMAGE g u SUBSET t
                   ==> homotopic_with (\x. T)
                       (subtopology euclidean u,subtopology euclidean t) f g)`;;

let RETRACT_OF_HOMOTOPICALLY_TRIVIAL_NULL = `!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on u /\ IMAGE f u SUBSET s
             ==> ?c. homotopic_with (\x. T)
                      (subtopology euclidean u,subtopology euclidean s)
                      f (\x. c))
        ==> (!f. f continuous_on u /\ IMAGE f u SUBSET t
                 ==> ?c. homotopic_with (\x. T)
                          (subtopology euclidean u,subtopology euclidean t)
                          f (\x. c))`;;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL = `!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f g. f continuous_on s /\ IMAGE f s SUBSET u /\
               g continuous_on s /\ IMAGE g s SUBSET u
               ==> homotopic_with (\x. T)
                    (subtopology euclidean s,subtopology euclidean u)  f g)
        ==> (!f g. f continuous_on t /\ IMAGE f t SUBSET u /\
                   g continuous_on t /\ IMAGE g t SUBSET u
                   ==> homotopic_with (\x. T)
                       (subtopology euclidean t,subtopology euclidean u) f g)`;;

let RETRACT_OF_COHOMOTOPICALLY_TRIVIAL_NULL = `!s t:real^N->bool u:real^M->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET u
             ==> ?c. homotopic_with (\x. T)
                      (subtopology euclidean s,subtopology euclidean u)
                      f (\x. c))
        ==> (!f. f continuous_on t /\ IMAGE f t SUBSET u
                 ==> ?c. homotopic_with (\x. T)
                          (subtopology euclidean t,subtopology euclidean u)
                          f (\x. c))`;;

let RETRACTION_IMP_QUOTIENT_MAP_EXPLICIT = `!r s t:real^N->bool.
    retraction (s,t) r
    ==> !u. u SUBSET t
            ==> (open_in (subtopology euclidean s) {x | x IN s /\ r x IN u} <=>
                 open_in (subtopology euclidean t) u)`;;

let RETRACT_OF_LOCALLY_CONNECTED = `!s t:real^N->bool.
        s retract_of t /\ locally connected t ==> locally connected s`;;

let RETRACT_OF_LOCALLY_PATH_CONNECTED = `!s t:real^N->bool.
        s retract_of t /\ locally path_connected t
        ==> locally path_connected s`;;

let RETRACT_OF_LOCALLY_COMPACT = `!s t:real^N->bool.
        locally compact s /\ t retract_of s ==> locally compact t`;;

let RETRACT_OF_PCROSS = `!s:real^M->bool s' t:real^N->bool t'.
        s retract_of s' /\ t retract_of t'
        ==> (s PCROSS t) retract_of (s' PCROSS t')`;;

let RETRACT_OF_PCROSS_EQ = `!s s':real^M->bool t t':real^N->bool.
        s PCROSS t retract_of s' PCROSS t' <=>
        (s = {} \/ t = {}) /\ (s' = {} \/ t' = {}) \/
        s retract_of s' /\ t retract_of t'`;;

let HOMOTOPIC_INTO_RETRACT = `!f:real^M->real^N g s t u.
        IMAGE f s SUBSET t /\ IMAGE g s SUBSET t /\ t retract_of u /\
        homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean u) f g
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean t) f g`;;

(* ------------------------------------------------------------------------- *)
(* Brouwer fixed-point theorem and related results.                          *)
(* ------------------------------------------------------------------------- *)

let CONTRACTIBLE_SPHERE = `!a:real^N r. contractible(sphere(a,r)) <=> r <= &0`;;

let NO_RETRACTION_CBALL = `!a:real^N e. &0 < e ==> ~(sphere(a,e) retract_of cball(a,e))`;;

let BROUWER_BALL = `!f:real^N->real^N a e.
        &0 < e /\
        f continuous_on cball(a,e) /\
        IMAGE f (cball(a,e)) SUBSET cball(a,e)
        ==> ?x. x IN cball(a,e) /\ f x = x`;;

let BROUWER = `!f:real^N->real^N s.
        compact s /\ convex s /\ ~(s = {}) /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`;;

let BROUWER_WEAK = `!f:real^N->real^N s.
        compact s /\ convex s /\ ~(interior s = {}) /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`;;

let BROUWER_CUBE = `!f:real^N->real^N.
        f continuous_on (interval [vec 0,vec 1]) /\
        IMAGE f (interval [vec 0,vec 1]) SUBSET (interval [vec 0,vec 1])
        ==> ?x. x IN interval[vec 0,vec 1] /\ f x = x`;;

(* ------------------------------------------------------------------------- *)
(* Now we can finally deduce what the topological dimension of R^n is.       *)
(* Proof following Hurewicz & Wallman's "dimension theory".                  *)
(* ------------------------------------------------------------------------- *)

let DIMENSION_EQ_AFF_DIM = `!s:real^N->bool. convex s ==> dimension s = aff_dim s`;;

let AFF_DIM_DIMENSION = `!s:real^N->bool. aff_dim s = dimension(affine hull s)`;;

let AFF_DIM_DIMENSION_ALT = `!s:real^N->bool. aff_dim s = dimension(convex hull s)`;;

let DIMENSION_SUBSPACE = `!s:real^N->bool. subspace s ==> dimension s = &(dim s)`;;

let DIM_DIMENSION = `!s:real^N->bool. &(dim s) = dimension(span s)`;;

let DIMENSION_OPEN_IN_CONVEX = `!u s:real^N->bool.
        convex u /\ open_in (subtopology euclidean u) s
        ==> dimension s = if s = {} then -- &1 else aff_dim u`;;

let DIMENSION_OPEN = `!s:real^N->bool.
        open s ==> dimension s = if s = {} then -- &1 else &(dimindex(:N))`;;

let DIMENSION_UNIV = `dimension(:real^N) = &(dimindex(:N))`;;

let DIMENSION_NONEMPTY_INTERIOR = `!s:real^N->bool. ~(interior s = {}) ==> dimension s = &(dimindex(:N))`;;

let DIMENSION_ATMOST_RATIONAL_COORDINATES = `!n. n <= dimindex(:N)
       ==> dimension
           {x:real^N | CARD {i | i IN 1..dimindex(:N) /\ rational(x$i)} <= n} =
           &n`;;

let DIMENSION_COMPLEMENT_RATIONAL_COORDINATES = `dimension((:real^N) DIFF
             { x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)}) =
   &(dimindex(:N)) - &1`;;

let DIMENSION_EQ_FULL_GEN = `!s:real^N->bool.
        dimension s = aff_dim s <=> s = {} \/ ~(relative_interior s = {})`;;

let DIMENSION_LT_FULL_GEN = `!s:real^N->bool. dimension s < aff_dim s <=>
                    ~(s = {}) /\ relative_interior s = {}`;;

let DIMENSION_EQ_FULL_ALT = `!u s:real^N->bool.
        convex u /\ s SUBSET u
        ==> (dimension s = aff_dim u <=>
             s = {} /\ u = {} \/
             ~(subtopology euclidean u interior_of s = {}))`;;

let DIMENSION_LT_FULL_ALT = `!u s:real^N->bool.
        convex u /\ s SUBSET u
        ==> (dimension s < aff_dim u <=>
             ~(u = {}) /\ subtopology euclidean u interior_of s = {})`;;

let DIMENSION_EQ_FULL = `!s:real^N->bool. dimension s = &(dimindex(:N)) <=> ~(interior s = {})`;;

let DIMENSION_LT_FULL = `!s:real^N->bool. dimension s < &(dimindex(:N)) <=> interior s = {}`;;

let DIMENSION_RELATIVE_FRONTIER_BOUNDED_OPEN = `!u s:real^N->bool.
        affine u /\ open_in (subtopology euclidean u) s /\ bounded s
        ==> dimension(relative_frontier s) =
            if s = {} then -- &1 else aff_dim u - &1`;;

let DIMENSION_FRONTIER_BOUNDED_OPEN = `!u:real^N->bool.
        open u /\ bounded u
        ==> dimension(frontier u) =
            if u = {} then -- &1 else &(dimindex(:N)) - &1`;;

let DIMENSION_RELATIVE_FRONTIER_NONDENSE_OPEN = `!u s:real^N->bool.
        affine u /\ open_in (subtopology euclidean u) s /\
        ~(s = {}) /\ ~(subtopology euclidean u closure_of s = u)
        ==> dimension(relative_frontier s) = aff_dim u - &1`;;

let DIMENSION_FRONTIER_NONDENSE_OPEN = `!u:real^N->bool.
        open u /\ ~(u = {}) /\ ~(closure u = (:real^N))
        ==> dimension(frontier u) = &(dimindex(:N)) - &1`;;

let DIMENSION_RELATIVE_FRONTIER_CONVEX = `!s:real^N->bool.
        convex s /\ bounded s /\ ~(s = {})
        ==> dimension(relative_frontier s) = aff_dim s - &1`;;

let DIMENSION_SPHERE_INTER_AFFINE = `!a:real^N r t.
        &0 < r /\ affine t /\ a IN t
        ==> dimension(sphere(a,r) INTER t) = aff_dim t - &1`;;

let DIMENSION_SPHERE = `!a:real^N r. dimension(sphere(a,r)) =
                if &0 < r then &(dimindex(:N)) - &1
                else if r = &0 then &0 else -- &1`;;

(* ------------------------------------------------------------------------- *)
(* Nonseparation: a "simple" set of dimension n can't be separated by sets   *)
(* of dimension <= n - 2.                                                    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_OPEN_IN_CONVEX_DIFF_LOWDIM = `!c s t:real^N->bool.
        convex c /\ open_in (subtopology euclidean c) s /\
        connected s /\ dimension t <= aff_dim c - &2
        ==> connected(s DIFF t)`;;

let CONNECTED_CONVEX_DIFF_LOWDIM = `!s t:real^N->bool.
        convex s /\ dimension t <= aff_dim s - &2 ==> connected(s DIFF t)`;;

let CONNECTED_OPEN_IN_DIFF_LOWDIM = `!s t:real^N->bool.
        open_in (subtopology euclidean (affine hull s)) s /\
        connected s /\
        dimension t <= aff_dim s - &2
        ==> connected(s DIFF t)`;;

let CONNECTED_OPEN_DIFF_LOWDIM = `!s t:real^N->bool.
        open s /\ connected s /\ dimension t <= &(dimindex(:N)) - &2
        ==> connected(s DIFF t)`;;

let CONNECTED_FULL_CONVEX_DIFF_LOWDIM = `!s:real^N->bool t.
        convex s /\ ~(interior s = {}) /\ dimension t <= &(dimindex(:N)) - &2
        ==> connected(s DIFF t)`;;

let CONNECTED_UNIV_DIFF_LOWDIM = `!s:real^N->bool.
        dimension s <= &(dimindex(:N)) - &2 ==> connected((:real^N) DIFF s)`;;

let CONNECTED_FULL_REGULAR_DIFF_LOWDIM = `!s:real^N->bool t.
        s SUBSET closure(interior s) /\
        connected(interior s) /\
        dimension t <= &(dimindex(:N)) - &2
        ==> connected(s DIFF t)`;;

(* ------------------------------------------------------------------------- *)
(* Absolute retracts (AR), absolute neighbourhood retracts (ANR) and also    *)
(* Euclidean neighbourhood retracts (ENR). We define AR and ANR by           *)
(* specializing the standard definitions for a set in R^n to embedding in    *)
(* spaces inside R^{n+1}. This turns out to be sufficient (since any set in  *)
(* R^n can be embedded as a closed subset of a convex subset of R^{n+1}) to  *)
(* derive the usual definitions, but we need to split them into two          *)
(* implications because of the lack of type quantifiers. Then ENR turns out  *)
(* to be equivalent to ANR plus local compactness.                           *)
(* ------------------------------------------------------------------------- *)

let AR = new_definition
 `AR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> s' retract_of u`;;

let ANR = new_definition
 `ANR(s:real^N->bool) <=>
        !u s':real^(N,1)finite_sum->bool.
                s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
                ==> ?t. open_in (subtopology euclidean u) t /\
                        s' retract_of t`;;

let ENR = new_definition
 `ENR s <=> ?u. open u /\ s retract_of u`;;

(* ------------------------------------------------------------------------- *)
(* First, show that we do indeed get the "usual" properties of ARs and ANRs. *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ABSOLUTE_EXTENSOR = `!f:real^M->real^N u t s.
        AR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                !x. x IN t ==> g x = f x`;;

let AR_IMP_ABSOLUTE_RETRACT = `!s:real^N->bool u s':real^M->bool.
        AR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> s' retract_of u`;;

let AR_IMP_ABSOLUTE_RETRACT_UNIV = `!s:real^N->bool s':real^M->bool.
    AR s /\ s homeomorphic s' /\ closed s' ==> s' retract_of (:real^M)`;;

let ABSOLUTE_EXTENSOR_IMP_AR = `!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)
        ==> AR s`;;

let AR_EQ_ABSOLUTE_EXTENSOR = `!s:real^N->bool.
        AR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?g. g continuous_on u /\ IMAGE g u SUBSET s /\
                     !x. x IN t ==> g x = f x)`;;

let AR_IMP_RETRACT = `!s u:real^N->bool.
        AR s /\ closed_in (subtopology euclidean u) s ==> s retract_of u`;;

let HOMEOMORPHIC_ARNESS = `!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (AR s <=> AR t)`;;

let AR_TRANSLATION = `!a:real^N s. AR(IMAGE (\x. a + x) s) <=> AR s`;;

add_translation_invariants [AR_TRANSLATION];;

let AR_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (AR(IMAGE f s) <=> AR s)`;;

add_linear_invariants [AR_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_ARNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (AR(IMAGE f k) <=> AR k)`;;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = `!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v g. t SUBSET v /\ open_in (subtopology euclidean u) v /\
                  g continuous_on v /\ IMAGE g v SUBSET s /\
                  !x. x IN t ==> g x = f x`;;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = `!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v. open_in (subtopology euclidean u) v /\
                s' retract_of v`;;

let ANR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = `!s:real^N->bool s':real^M->bool.
    ANR s /\ s homeomorphic s' /\ closed s' ==> ?v. open v /\ s' retract_of v`;;

let ABSOLUTE_NEIGHBOURHOOD_EXTENSOR_IMP_ANR = `!s:real^N->bool.
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)
        ==> ANR s`;;

let ANR_EQ_ABSOLUTE_NEIGHBOURHOOD_EXTENSOR = `!s:real^N->bool.
        ANR s <=>
        (!f:real^(N,1)finite_sum->real^N u t.
             f continuous_on t /\ IMAGE f t SUBSET s /\
             closed_in (subtopology euclidean u) t
             ==> ?v g. t SUBSET v /\ open_in  (subtopology euclidean u) v /\
                       g continuous_on v /\ IMAGE g v SUBSET s /\
                       !x. x IN t ==> g x = f x)`;;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_RETRACT = `!s:real^N->bool u s':real^M->bool.
        ANR s /\ s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s' SUBSET v /\ v SUBSET w /\ s' retract_of w`;;

let ANR_IMP_ABSOLUTE_CLOSED_NEIGHBOURHOOD_EXTENSOR = `!f:real^M->real^N u t s.
        ANR s /\ f continuous_on t /\ IMAGE f t SUBSET s /\
        closed_in (subtopology euclidean u) t
        ==> ?v w g. open_in (subtopology euclidean u) v /\
                    closed_in (subtopology euclidean u) w /\
                    t SUBSET v /\ v SUBSET w /\
                    g continuous_on w /\ IMAGE g w SUBSET s /\
                    !x. x IN t ==> g x = f x`;;

let ANR_IMP_NEIGHBOURHOOD_RETRACT = `!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v. open_in (subtopology euclidean u) v /\
                s retract_of v`;;

let ANR_IMP_CLOSED_NEIGHBOURHOOD_RETRACT = `!s:real^N->bool u.
        ANR s /\ closed_in (subtopology euclidean u) s
        ==> ?v w. open_in (subtopology euclidean u) v /\
                  closed_in (subtopology euclidean u) w /\
                  s SUBSET v /\ v SUBSET w /\ s retract_of w`;;

let HOMEOMORPHIC_ANRNESS = `!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ANR s <=> ANR t)`;;

let ANR_TRANSLATION = `!a:real^N s. ANR(IMAGE (\x. a + x) s) <=> ANR s`;;

add_translation_invariants [ANR_TRANSLATION];;

let ANR_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ANR(IMAGE f s) <=> ANR s)`;;

add_linear_invariants [ANR_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_ANRNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (ANR(IMAGE f k) <=> ANR k)`;;

let HOMOTOPIC_ON_NEIGHBOURHOOD_INTO_ANR = `!f g:real^M->real^N s t v.
        ANR v /\
        f continuous_on s /\ IMAGE f s SUBSET v /\
        g continuous_on s /\ IMAGE g s SUBSET v /\
        t SUBSET s /\ (!x. x IN t ==> f x = g x)
        ==> ?u. open_in (subtopology euclidean s) u /\ t SUBSET u /\
                homotopic_with (\h. !x. x IN t ==> h x = f x)
                 (subtopology euclidean u,subtopology euclidean v) f g`;;

(* ------------------------------------------------------------------------- *)
(* Analogous properties of ENRs.                                             *)
(* ------------------------------------------------------------------------- *)

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT = `!s:real^M->bool s':real^N->bool u.
        ENR s /\ s homeomorphic s' /\ s' SUBSET u
        ==> ?t'. open_in (subtopology euclidean u) t' /\ s' retract_of t'`;;

let ENR_IMP_ABSOLUTE_NEIGHBOURHOOD_RETRACT_UNIV = `!s:real^M->bool s':real^N->bool.
        ENR s /\ s homeomorphic s' ==> ?t'. open t' /\ s' retract_of t'`;;

let HOMEOMORPHIC_ENRNESS = `!s:real^M->bool t:real^N->bool.
      s homeomorphic t ==> (ENR s <=> ENR t)`;;

let ENR_TRANSLATION = `!a:real^N s. ENR(IMAGE (\x. a + x) s) <=> ENR s`;;

add_translation_invariants [ENR_TRANSLATION];;

let ENR_LINEAR_IMAGE_EQ = `!f:real^M->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (ENR(IMAGE f s) <=> ENR s)`;;

add_linear_invariants [ENR_LINEAR_IMAGE_EQ];;

let HOMEOMORPHISM_ENRNESS = `!f:real^M->real^N g s t k.
        homeomorphism (s,t) (f,g) /\ k SUBSET s
        ==> (ENR(IMAGE f k) <=> ENR k)`;;

(* ------------------------------------------------------------------------- *)
(* Some relations among the concepts. We also relate AR to being a retract   *)
(* of UNIV, which is often a more convenient proxy in the closed case.       *)
(* ------------------------------------------------------------------------- *)

let AR_IMP_ANR = `!s:real^N->bool. AR s ==> ANR s`;;

let ENR_IMP_ANR = `!s:real^N->bool. ENR s ==> ANR s`;;

let ENR_ANR = `!s:real^N->bool. ENR s <=> ANR s /\ locally compact s`;;

let AR_ANR = `!s:real^N->bool. AR s <=> ANR s /\ contractible s /\ ~(s = {})`;;

let ANR_RETRACT_OF_ANR = `!s t:real^N->bool. ANR t /\ s retract_of t ==> ANR s`;;

let AR_RETRACT_OF_AR = `!s t:real^N->bool. AR t /\ s retract_of t ==> AR s`;;

let ENR_RETRACT_OF_ENR = `!s t:real^N->bool. ENR t /\ s retract_of t ==> ENR s`;;

let RETRACT_OF_UNIV = `!s:real^N->bool. s retract_of (:real^N) <=> AR s /\ closed s`;;

let COMPACT_AR = `!s. compact s /\ AR s <=> compact s /\ s retract_of (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* More properties of ARs, ANRs and ENRs.                                    *)
(* ------------------------------------------------------------------------- *)

let NOT_AR_EMPTY = `~(AR({}:real^N->bool))`;;

let AR_IMP_NONEMPTY = `!s:real^N->bool. AR s ==> ~(s = {})`;;

let ENR_EMPTY = `ENR {}`;;

let ANR_EMPTY = `ANR {}`;;

let CONVEX_IMP_AR = `!s:real^N->bool. convex s /\ ~(s = {}) ==> AR s`;;

let CONVEX_IMP_ANR = `!s:real^N->bool. convex s ==> ANR s`;;

let IS_INTERVAL_IMP_ENR = `!s:real^N->bool. is_interval s ==> ENR s`;;

let ENR_CONVEX_CLOSED = `!s:real^N->bool. closed s /\ convex s ==> ENR s`;;

let AR_UNIV = `AR(:real^N)`;;

let ANR_UNIV = `ANR(:real^N)`;;

let ENR_UNIV = `ENR(:real^N)`;;

let AR_SING = `!a:real^N. AR {a}`;;

let ANR_SING = `!a:real^N. ANR {a}`;;

let ENR_SING = `!a:real^N. ENR {a}`;;

let ANR_OPEN_IN = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ ANR t ==> ANR s`;;

let ENR_OPEN_IN = `!s t:real^N->bool.
        open_in (subtopology euclidean t) s /\ ENR t ==> ENR s`;;

let ANR_NEIGHBORHOOD_RETRACT = `!s t u:real^N->bool.
        s retract_of t /\ open_in (subtopology euclidean u) t /\ ANR u
        ==> ANR s`;;

let ENR_NEIGHBORHOOD_RETRACT = `!s t u:real^N->bool.
        s retract_of t /\ open_in (subtopology euclidean u) t /\ ENR u
        ==> ENR s`;;

let ANR_RELATIVE_INTERIOR = `!s. ANR(s) ==> ANR(relative_interior s)`;;

let ANR_DELETE = `!s a:real^N. ANR(s) ==> ANR(s DELETE a)`;;

let ENR_RELATIVE_INTERIOR = `!s. ENR(s) ==> ENR(relative_interior s)`;;

let ENR_DELETE = `!s a:real^N. ENR(s) ==> ENR(s DELETE a)`;;

let OPEN_IMP_ENR = `!s:real^N->bool. open s ==> ENR s`;;

let OPEN_IMP_ANR = `!s:real^N->bool. open s ==> ANR s`;;

let ANR_BALL = `!a:real^N r. ANR(ball(a,r))`;;

let ENR_BALL = `!a:real^N r. ENR(ball(a,r))`;;

let AR_BALL = `!a:real^N r. AR(ball(a,r)) <=> &0 < r`;;

let ANR_CBALL = `!a:real^N r. ANR(cball(a,r))`;;

let ENR_CBALL = `!a:real^N r. ENR(cball(a,r))`;;

let AR_CBALL = `!a:real^N r. AR(cball(a,r)) <=> &0 <= r`;;

let ANR_INTERVAL = `(!a b:real^N. ANR(interval[a,b])) /\ (!a b:real^N. ANR(interval(a,b)))`;;

let ENR_INTERVAL = `(!a b:real^N. ENR(interval[a,b])) /\ (!a b:real^N. ENR(interval(a,b)))`;;

let AR_INTERVAL = `(!a b:real^N. AR(interval[a,b]) <=> ~(interval[a,b] = {})) /\
   (!a b:real^N. AR(interval(a,b)) <=> ~(interval(a,b) = {}))`;;

let ANR_INTERIOR = `!s. ANR(interior s)`;;

let ENR_INTERIOR = `!s. ENR(interior s)`;;

let AR_IMP_CONTRACTIBLE = `!s:real^N->bool. AR s ==> contractible s`;;

let AR_IMP_PATH_CONNECTED = `!s:real^N->bool. AR s ==> path_connected s`;;

let AR_IMP_CONNECTED = `!s:real^N->bool. AR s ==> connected s`;;

let ENR_IMP_LOCALLY_COMPACT = `!s:real^N->bool. ENR s ==> locally compact s`;;

let ANR_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool. ANR s ==> locally path_connected s`;;

let ANR_IMP_LOCALLY_CONNECTED = `!s:real^N->bool. ANR s ==> locally connected s`;;

let AR_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool. AR s ==> locally path_connected s`;;

let AR_IMP_LOCALLY_CONNECTED = `!s:real^N->bool. AR s ==> locally connected s`;;

let ENR_IMP_LOCALLY_PATH_CONNECTED = `!s:real^N->bool. ENR s ==> locally path_connected s`;;

let ENR_IMP_LOCALLY_CONNECTED = `!s:real^N->bool. ENR s ==> locally connected s`;;

let COUNTABLE_ANR_COMPONENTS = `!s:real^N->bool. ANR s ==> COUNTABLE(components s)`;;

let COUNTABLE_ANR_CONNECTED_COMPONENTS = `!s:real^N->bool t.
        ANR s ==> COUNTABLE {connected_component s x | x IN t}`;;

let COUNTABLE_ANR_PATH_COMPONENTS = `!s:real^N->bool t.
        ANR s ==> COUNTABLE {path_component s x | x IN t}`;;

let FINITE_ANR_COMPONENTS = `!s:real^N->bool. ANR s /\ compact s ==> FINITE(components s)`;;

let FINITE_ENR_COMPONENTS = `!s:real^N->bool. ENR s /\ compact s ==> FINITE(components s)`;;

let ANR_PCROSS = `!s:real^M->bool t:real^N->bool. ANR s /\ ANR t ==> ANR(s PCROSS t)`;;

let ANR_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        ANR(s PCROSS t) <=> s = {} \/ t = {} \/ ANR s /\ ANR t`;;

let AR_PCROSS = `!s:real^M->bool t:real^N->bool. AR s /\ AR t ==> AR(s PCROSS t)`;;

let ENR_PCROSS = `!s:real^M->bool t:real^N->bool. ENR s /\ ENR t ==> ENR(s PCROSS t)`;;

let ENR_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        ENR(s PCROSS t) <=> s = {} \/ t = {} \/ ENR s /\ ENR t`;;

let AR_PCROSS_EQ = `!s:real^M->bool t:real^N->bool.
        AR(s PCROSS t) <=> AR s /\ AR t /\ ~(s = {}) /\ ~(t = {})`;;

let AR_CLOSED_UNION_LOCAL = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s) /\ AR(t) /\ AR(s INTER t)
        ==> AR(s UNION t)`;;

(* ------------------------------------------------------------------------- *)
(* General ANR union lemma (Kuratowski).                                     *)
(* ------------------------------------------------------------------------- *)

let ANR_UNION_EXTENSION_LEMMA = `!f:real^M->real^N s t u s1 s2 u1 u2.
        f continuous_on t /\ IMAGE f t SUBSET u /\
        ANR u1 /\ ANR u2 /\ ANR(u1 INTER u2) /\ u1 UNION u2 = u /\
        closed_in (subtopology euclidean s) t /\
        closed_in (subtopology euclidean s) s1 /\
        closed_in (subtopology euclidean s) s2 /\
        s1 UNION s2 = s /\
        IMAGE f (t INTER s1) SUBSET u1 /\
        IMAGE f (t INTER s2) SUBSET u2
        ==> ?v g. t SUBSET v /\
                  open_in (subtopology euclidean s) v /\
                  g continuous_on v /\ IMAGE g v SUBSET u /\
                  !x. x IN t ==> g x = f x`;;

(* ------------------------------------------------------------------------- *)
(* Application to closed union.                                              *)
(* ------------------------------------------------------------------------- *)

let ANR_CLOSED_UNION_LOCAL = `!s t:real^N->bool u.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        ANR(s) /\ ANR(t) /\ ANR(s INTER t)
        ==> ANR(s UNION t)`;;

let ENR_CLOSED_UNION_LOCAL = `!s t u:real^N->bool.
        closed_in (subtopology euclidean u) s /\
        closed_in (subtopology euclidean u) t /\
        ENR(s) /\ ENR(t) /\ ENR(s INTER t)
        ==> ENR(s UNION t)`;;

let AR_CLOSED_UNION = `!s t:real^N->bool.
        closed s /\ closed t /\ AR(s) /\ AR(t) /\ AR(s INTER t)
        ==> AR(s UNION t)`;;

let ANR_CLOSED_UNION = `!s t:real^N->bool.
        closed s /\ closed t /\ ANR(s) /\ ANR(t) /\ ANR(s INTER t)
        ==> ANR(s UNION t)`;;

let ENR_CLOSED_UNION = `!s t:real^N->bool.
        closed s /\ closed t /\ ENR(s) /\ ENR(t) /\ ENR(s INTER t)
        ==> ENR(s UNION t)`;;

let ABSOLUTE_RETRACT_UNION = `!s t. s retract_of (:real^N) /\
         t retract_of (:real^N) /\
         (s INTER t) retract_of (:real^N)
         ==> (s UNION t) retract_of (:real^N)`;;

let RETRACT_FROM_UNION_AND_INTER = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        (s UNION t) retract_of u /\ (s INTER t) retract_of t
        ==> s retract_of u`;;

let AR_FROM_UNION_AND_INTER_LOCAL = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s) /\ AR(t)`;;

let AR_FROM_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\ closed t /\ AR(s UNION t) /\ AR(s INTER t)
        ==> AR(s) /\ AR(t)`;;

let ANR_FROM_UNION_AND_INTER_LOCAL = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s) /\ ANR(t)`;;

let ANR_FROM_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\ closed t /\ ANR(s UNION t) /\ ANR(s INTER t)
        ==> ANR(s) /\ ANR(t)`;;

let ANR_FINITE_UNIONS_CONVEX_CLOSED = `!t:(real^N->bool)->bool.
        FINITE t /\ (!c. c IN t ==> closed c /\ convex c) ==> ANR(UNIONS t)`;;

let FINITE_IMP_ANR = `!s:real^N->bool. FINITE s ==> ANR s`;;

let ANR_INSERT = `!s a:real^N. closed s /\ ANR s ==> ANR(a INSERT s)`;;

let ANR_TRIANGULATION = `!tr. triangulation tr ==> ANR(UNIONS tr)`;;

let ANR_SIMPLICIAL_COMPLEX = `!c. simplicial_complex c ==>  ANR(UNIONS c)`;;

let ANR_PATH_COMPONENT_ANR = `!s x:real^N. ANR(s) ==> ANR(path_component s x)`;;

let ANR_CONNECTED_COMPONENT_ANR = `!s x:real^N. ANR(s) ==> ANR(connected_component s x)`;;

let ANR_COMPONENT_ANR = `!s:real^N->bool.
        ANR s /\ c IN components s ==> ANR c`;;

(* ------------------------------------------------------------------------- *)
(* Application to open union.                                                *)
(* ------------------------------------------------------------------------- *)

let ANR_OPEN_UNION = `!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t /\
        ANR(s) /\ ANR(t)
        ==> ANR(s UNION t)`;;

let ENR_OPEN_UNION = `!s t u:real^N->bool.
        open_in (subtopology euclidean u) s /\
        open_in (subtopology euclidean u) t /\
        ENR(s) /\ ENR(t)
        ==> ENR(s UNION t)`;;

let ANR_OPEN_UNIONS = `!f:(real^N->bool)->bool u.
        (!s. s IN f ==> ANR s) /\
        (!s. s IN f ==> open_in (subtopology euclidean u) s)
        ==> ANR(UNIONS f)`;;

let ENR_OPEN_UNIONS = `!f:(real^N->bool)->bool u.
        (!s. s IN f ==> ENR s) /\
        (!s. s IN f ==> open_in (subtopology euclidean u) s)
        ==> ENR(UNIONS f)`;;

let LOCALLY_ANR_ALT = `!s:real^N->bool.
        locally ANR s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\ ANR u /\
                      x IN u /\ u SUBSET v`;;

let LOCALLY_ANR = `!s:real^N->bool.
        locally ANR s <=>
        !x. x IN s
            ==> ?v. x IN v /\ open_in (subtopology euclidean s) v /\ ANR v`;;

let ANR_LOCALLY = `!s:real^N->bool. locally ANR s <=> ANR s`;;

let LOCALLY_ENR_ALT = `!s:real^N->bool.
        locally ENR s <=>
        !v x. open_in (subtopology euclidean s) v /\ x IN v
              ==> ?u. open_in (subtopology euclidean s) u /\ ENR u /\
                      x IN u /\ u SUBSET v`;;

let LOCALLY_ENR = `!s:real^N->bool.
        locally ENR s <=>
        !x. x IN s
            ==> ?v. x IN v /\ open_in (subtopology euclidean s) v /\ ENR v`;;

let ENR_LOCALLY = `!s:real^N->bool. locally ENR s <=> ENR s`;;

let ANR_COVERING_SPACE_EQ = `!p:real^M->real^N s c.
        covering_space (c,p) s ==> (ANR s <=> ANR c)`;;

let ANR_COVERING_SPACE = `!p:real^M->real^N s c.
        covering_space (c,p) s /\ ANR c ==> ANR s`;;

let ENR_COVERING_SPACE_EQ = `!p:real^M->real^N s c.
        covering_space (c,p) s ==> (ENR s <=> ENR c)`;;

let ENR_COVERING_SPACE = `!p:real^M->real^N s c.
        covering_space (c,p) s /\ ENR c ==> ENR s`;;

(* ------------------------------------------------------------------------- *)
(* Original ANR material, now for ENRs. Eventually more of this will be      *)
(* updated and generalized for AR and ANR as well.                           *)
(* ------------------------------------------------------------------------- *)

let ENR_BOUNDED = `!s:real^N->bool.
        bounded s
        ==> (ENR s <=> ?u. open u /\ bounded u /\ s retract_of u)`;;

let ABSOLUTE_RETRACT_IMP_AR_GEN = `!s:real^M->bool s':real^N->bool t u.
      s retract_of t /\ convex t /\ ~(t = {}) /\
      s homeomorphic s' /\ closed_in (subtopology euclidean u) s'
      ==> s' retract_of u`;;

let ABSOLUTE_RETRACT_IMP_AR = `!s s'. s retract_of (:real^M) /\ s homeomorphic s' /\ closed s'
          ==> s' retract_of (:real^N)`;;

let HOMEOMORPHIC_COMPACT_ARNESS = `!s s'. s homeomorphic s'
          ==> (compact s /\ s retract_of (:real^M) <=>
               compact s' /\ s' retract_of (:real^N))`;;

let EXTENSION_INTO_AR_LOCAL = `!f:real^M->real^N c s t.
        f continuous_on c /\ IMAGE f c SUBSET t /\ t retract_of (:real^N) /\
        closed_in (subtopology euclidean s) c
        ==> ?g. g continuous_on s /\ IMAGE g (:real^M) SUBSET t /\
                !x. x IN c ==> g x = f x`;;

let EXTENSION_INTO_AR = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ t retract_of (:real^N) /\
        closed s
        ==> ?g. g continuous_on (:real^M) /\ IMAGE g (:real^M) SUBSET t /\
                !x. x IN s ==> g x = f x`;;

let NEIGHBOURHOOD_EXTENSION_INTO_ANR = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\ ANR t /\ closed s
        ==> ?v g. s SUBSET v /\ open v /\ g continuous_on v /\
                  IMAGE g v SUBSET t /\ !x. x IN s ==> g x = f x`;;

let EXTENSION_FROM_COMPONENT = `!f:real^M->real^N s c u.
        (locally connected s \/ compact s /\ ANR u) /\
        c IN components s /\
        f continuous_on c /\ IMAGE f c SUBSET u
        ==> ?g. g continuous_on s /\ IMAGE g s SUBSET u /\
                !x. x IN c ==> g x = f x`;;

let ABSOLUTE_RETRACT_FROM_UNION_AND_INTER = `!s t. (s UNION t) retract_of (:real^N) /\
         (s INTER t) retract_of (:real^N) /\
         closed s /\ closed t
         ==> s retract_of (:real^N)`;;

let COUNTABLE_ENR_COMPONENTS = `!s:real^N->bool. ENR s ==> COUNTABLE(components s)`;;

let COUNTABLE_ENR_CONNECTED_COMPONENTS = `!s:real^N->bool t.
        ENR s ==> COUNTABLE {connected_component s x | x | x IN t}`;;

let COUNTABLE_ENR_PATH_COMPONENTS = `!s:real^N->bool.
        ENR s ==> COUNTABLE {path_component s x | x | x IN s}`;;

let ENR_FROM_UNION_AND_INTER_GEN = `!s t:real^N->bool.
        closed_in (subtopology euclidean (s UNION t)) s /\
        closed_in (subtopology euclidean (s UNION t)) t /\
        ENR(s UNION t) /\ ENR(s INTER t)
        ==> ENR s`;;

let ENR_FROM_UNION_AND_INTER = `!s t:real^N->bool.
        closed s /\ closed t /\ ENR(s UNION t) /\ ENR(s INTER t)
        ==> ENR s`;;

let ENR_CLOSURE_FROM_FRONTIER = `!s:real^N->bool. ENR(frontier s) ==> ENR(closure s)`;;

let ANR_CLOSURE_FROM_FRONTIER = `!s:real^N->bool. ANR(frontier s) ==> ANR(closure s)`;;

let ENR_FINITE_UNIONS_CONVEX_CLOSED = `!t:(real^N->bool)->bool.
        FINITE t /\ (!c. c IN t ==> closed c /\ convex c) ==> ENR(UNIONS t)`;;

let FINITE_IMP_ENR = `!s:real^N->bool. FINITE s ==> ENR s`;;

let ENR_INSERT = `!s a:real^N. closed s /\ ENR s ==> ENR(a INSERT s)`;;

let ENR_TRIANGULATION = `!tr. triangulation tr ==> ENR(UNIONS tr)`;;

let ENR_SIMPLICIAL_COMPLEX = `!c. simplicial_complex c ==>  ENR(UNIONS c)`;;

let ENR_PATH_COMPONENT_ENR = `!s x:real^N. ENR(s) ==> ENR(path_component s x)`;;

let ENR_CONNECTED_COMPONENT_ENR = `!s x:real^N. ENR(s) ==> ENR(connected_component s x)`;;

let ENR_COMPONENT_ENR = `!s:real^N->bool.
        ENR s /\ c IN components s ==> ENR c`;;

let ENR_INTER_CLOSED_OPEN = `!s:real^N->bool. ENR s ==> ?t u. closed t /\ open u /\ s = t INTER u`;;

let ENR_IMP_FSGIMA = `!s:real^N->bool. ENR s ==> fsigma s`;;

let ENR_IMP_GDELTA = `!s:real^N->bool. ENR s ==> gdelta s`;;

let IS_INTERVAL_IMP_FSIGMA = `!s:real^N->bool. is_interval s ==> fsigma s`;;

let IS_INTERVAL_IMP_GDELTA = `!s:real^N->bool. is_interval s ==> gdelta s`;;

let IS_INTERVAL_IMP_BAIRE1_INDICATOR = `!s. is_interval s ==> baire 1 (:real^N) (indicator s)`;;

let ANR_COMPONENTWISE = `!s:real^N->bool.
        ANR s <=>
        COUNTABLE(components s) /\
        !c. c IN components s
            ==> open_in (subtopology euclidean s) c /\ ANR c`;;

let ENR_COMPONENTWISE = `!s:real^N->bool.
        ENR s <=>
        COUNTABLE(components s) /\
        !c. c IN components s
            ==> open_in (subtopology euclidean s) c /\ ENR c`;;

let ABSOLUTE_RETRACT_HOMEOMORPHIC_CONVEX_COMPACT = `!s:real^N->bool t u:real^M->bool.
        s homeomorphic u /\ ~(s = {}) /\ s SUBSET t /\ convex u /\ compact u
        ==> s retract_of t`;;

let ABSOLUTE_RETRACT_PATH_IMAGE_ARC = `!g s:real^N->bool.
        arc g /\ path_image g SUBSET s ==> (path_image g) retract_of s`;;

let AR_ARC_IMAGE = `!g:real^1->real^N. arc g ==> AR(path_image g)`;;

let RELATIVE_FRONTIER_DEFORMATION_RETRACT_OF_PUNCTURED_CONVEX = `!s t a:real^N.
        convex s /\ convex t /\ bounded s /\ a IN relative_interior s /\
        relative_frontier s SUBSET t /\ t SUBSET affine hull s
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean (t DELETE a),
                  subtopology euclidean (t DELETE a)) (\x. x) r /\
                retraction (t DELETE a,relative_frontier s) r /\
                (!x. ?c. &0 < c /\ r(x) - a = c % (x - a))`;;

let RELATIVE_FRONTIER_RETRACT_OF_PUNCTURED_AFFINE_HULL = `!s a:real^N.
        convex s /\ bounded s /\ a IN relative_interior s
        ==> relative_frontier s retract_of (affine hull s DELETE a)`;;

let RELATIVE_BOUNDARY_RETRACT_OF_PUNCTURED_AFFINE_HULL = `!s a:real^N.
        convex s /\ compact s /\ a IN relative_interior s
        ==> (s DIFF relative_interior s) retract_of
            (affine hull s DELETE a)`;;

let PATH_CONNECTED_SPHERE_GEN = `!s:real^N->bool.
        convex s /\ bounded s /\ ~(aff_dim s = &1)
        ==> path_connected(relative_frontier s)`;;

let CONNECTED_SPHERE_GEN = `!s:real^N->bool.
        convex s /\ bounded s /\ ~(aff_dim s = &1)
        ==> connected(relative_frontier s)`;;

let ENR_RELATIVE_FRONTIER_CONVEX = `!s:real^N->bool. bounded s /\ convex s ==> ENR(relative_frontier s)`;;

let ANR_RELATIVE_FRONTIER_CONVEX = `!s:real^N->bool. bounded s /\ convex s ==> ANR(relative_frontier s)`;;

let FRONTIER_RETRACT_OF_PUNCTURED_UNIVERSE = `!s a. convex s /\ bounded s /\ a IN interior s
         ==> (frontier s) retract_of ((:real^N) DELETE a)`;;

let SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE_GEN = `!a r b:real^N.
      b IN ball(a,r) ==> sphere(a,r) retract_of ((:real^N) DELETE b)`;;

let SPHERE_RETRACT_OF_PUNCTURED_UNIVERSE = `!a r. &0 < r ==> sphere(a,r) retract_of ((:real^N) DELETE a)`;;

let ENR_SPHERE = `!a:real^N r. ENR(sphere(a,r))`;;

let ANR_SPHERE = `!a:real^N r. ANR(sphere(a,r))`;;

let LOCALLY_PATH_CONNECTED_SPHERE_GEN = `!s:real^N->bool.
       bounded s /\ convex s ==> locally path_connected (relative_frontier s)`;;

let LOCALLY_CONNECTED_SPHERE_GEN = `!s:real^N->bool.
       bounded s /\ convex s ==> locally connected (relative_frontier s)`;;

let ABSOLUTE_RETRACTION_CONVEX_CLOSED_RELATIVE = `!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> ?r. retraction (t,s) r /\
                !x. x IN (affine hull s) DIFF (relative_interior s)
                    ==> r(x) IN relative_frontier s`;;

let ABSOLUTE_RETRACTION_CONVEX_CLOSED = `!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> ?r. retraction (t,s) r /\
                (!x. ~(x IN s) ==> r(x) IN frontier s)`;;

let ABSOLUTE_RETRACT_CONVEX_CLOSED = `!s:real^N->bool t.
        convex s /\ closed s /\ ~(s = {}) /\ s SUBSET t
        ==> s retract_of t`;;

let ABSOLUTE_RETRACT_CONVEX = `!s u:real^N->bool.
        convex s /\ ~(s = {}) /\ closed_in (subtopology euclidean u) s
        ==> s retract_of u`;;

let ENR_PATH_IMAGE_SIMPLE_PATH = `!g:real^1->real^N. simple_path g ==> ENR(path_image g)`;;

let ANR_PATH_IMAGE_SIMPLE_PATH = `!g:real^1->real^N. simple_path g ==> ANR(path_image g)`;;

(* ------------------------------------------------------------------------- *)
(* Borsuk homotopy extension thorem. It's only this late so we can use the   *)
(* concept of retraction, saying that the domain sets or range set are ANRs. *)
(* ------------------------------------------------------------------------- *)

let BORSUK_HOMOTOPY_EXTENSION_HOMOTOPIC = `!f:real^M->real^N g s t u.
        closed_in (subtopology euclidean t) s /\
        (ANR s /\ ANR t \/ ANR u) /\
        f continuous_on t /\ IMAGE f t SUBSET u /\
        homotopic_with (\x. T)
          (subtopology euclidean s,subtopology euclidean u) f g
        ==> ?g'. homotopic_with (\x. T)
                  (subtopology euclidean t,subtopology euclidean u) f g' /\
                 g' continuous_on t /\ IMAGE g' t SUBSET u /\
                 !x. x IN s ==> g'(x) = g(x)`;;

let BORSUK_HOMOTOPY_EXTENSION = `!f:real^M->real^N g s t u.
        closed_in (subtopology euclidean t) s /\
        (ANR s /\ ANR t \/ ANR u) /\
        f continuous_on t /\ IMAGE f t SUBSET u /\
        homotopic_with (\x. T)
         (subtopology euclidean s,subtopology euclidean u) f g
        ==> ?g'. g' continuous_on t /\ IMAGE g' t SUBSET u /\
                 !x. x IN s ==> g'(x) = g(x)`;;

let NULLHOMOTOPIC_INTO_ANR_EXTENSION = `!f:real^M->real^N s t.
      closed s /\ f continuous_on s /\ ~(s = {}) /\ IMAGE f s SUBSET t /\ ANR t
      ==> ((?c. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean t)
                 f (\x. c)) <=>
           (?g. g continuous_on (:real^M) /\
                IMAGE g (:real^M) SUBSET t /\
                !x. x IN s ==> g x = f x))`;;

let NULLHOMOTOPIC_INTO_RELATIVE_FRONTIER_EXTENSION = `!f:real^M->real^N s t.
        closed s /\ f continuous_on s /\ ~(s = {}) /\
        IMAGE f s SUBSET relative_frontier t /\ convex t /\ bounded t
        ==> ((?c. homotopic_with (\x. T)
                   (subtopology euclidean s,
                    subtopology euclidean  (relative_frontier t)) f (\x. c)) <=>
             (?g. g continuous_on (:real^M) /\
                  IMAGE g (:real^M) SUBSET relative_frontier t /\
                  !x. x IN s ==> g x = f x))`;;

let NULLHOMOTOPIC_INTO_SPHERE_EXTENSION = `!f:real^M->real^N s a r.
     closed s /\ f continuous_on s /\ ~(s = {}) /\ IMAGE f s SUBSET sphere(a,r)
     ==> ((?c. homotopic_with (\x. T)
                (subtopology euclidean s,
                 subtopology euclidean (sphere(a,r))) f (\x. c)) <=>
          (?g. g continuous_on (:real^M) /\
               IMAGE g (:real^M) SUBSET sphere(a,r) /\
               !x. x IN s ==> g x = f x))`;;

let ABSOLUTE_RETRACT_CONTRACTIBLE_ANR = `!s u:real^N->bool.
      closed_in (subtopology euclidean u) s /\
      contractible s /\ ~(s = {}) /\ ANR s
      ==> s retract_of u`;;

(* ------------------------------------------------------------------------- *)
(* More homotopy extension results and relations to components.              *)
(* ------------------------------------------------------------------------- *)

let HOMOTOPIC_ON_COMPONENTS = `!s t f g:real^M->real^N.
        locally connected s /\
        (!c. c IN components s
             ==> homotopic_with (\x. T)
                   (subtopology euclidean c,subtopology euclidean t) f g)
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean t) f g`;;

let INESSENTIAL_ON_COMPONENTS = `!f:real^M->real^N s t.
        locally connected s /\ path_connected t /\
        (!c. c IN components s
             ==> ?a. homotopic_with (\x. T)
                       (subtopology euclidean c,subtopology euclidean t)
                       f (\x. a))
        ==> ?a. homotopic_with (\x. T)
                  (subtopology euclidean s,subtopology euclidean t)
                  f (\x. a)`;;

let HOMOTOPIC_NEIGHBOURHOOD_EXTENSION = `!f g:real^M->real^N s t u.
        f continuous_on s /\ IMAGE f s SUBSET u /\
        g continuous_on s /\ IMAGE g s SUBSET u /\
        closed_in (subtopology euclidean s) t /\ ANR u /\
        homotopic_with (\x. T)
         (subtopology euclidean t,subtopology euclidean u) f g
        ==> ?v. t SUBSET v /\
                open_in (subtopology euclidean s) v /\
                homotopic_with (\x. T)
                 (subtopology euclidean v,subtopology euclidean u) f g`;;

let HOMOTOPIC_ON_COMPONENTS_EQ = `!s t f g:real^M->real^N.
        (locally connected s \/ compact s /\ ANR t)
        ==> (homotopic_with (\x. T)
               (subtopology euclidean s,subtopology euclidean t) f g <=>
             f continuous_on s /\ IMAGE f s SUBSET t /\
             g continuous_on s /\ IMAGE g s SUBSET t /\
             !c. c IN components s
                 ==> homotopic_with (\x. T)
                      (subtopology euclidean c,subtopology euclidean t) f g)`;;

let INESSENTIAL_ON_COMPONENTS_EQ = `!s t f:real^M->real^N.
        (locally connected s \/ compact s /\ ANR t) /\
        path_connected t
        ==> ((?a. homotopic_with (\x. T)
                   (subtopology euclidean s,subtopology euclidean t)
                   f (\x. a)) <=>
             f continuous_on s /\ IMAGE f s SUBSET t /\
             !c. c IN components s
                 ==> ?a. homotopic_with (\x. T)
                          (subtopology euclidean c,subtopology euclidean t)
                          f (\x. a))`;;

let COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS = `!s:real^M->bool t:real^N->bool.
        (locally connected s \/ compact s /\ ANR t)
         ==> ((!f g. f continuous_on s /\ IMAGE f s SUBSET t /\
                     g continuous_on s /\ IMAGE g s SUBSET t
                     ==> homotopic_with (\x. T)
                          (subtopology euclidean s,subtopology euclidean t)
                          f g) <=>
              (!c. c IN components s
                   ==> (!f g. f continuous_on c /\ IMAGE f c SUBSET t /\
                              g continuous_on c /\ IMAGE g c SUBSET t
                              ==> homotopic_with (\x. T)
                                   (subtopology euclidean c,
                                    subtopology euclidean t) f g)))`;;

let COHOMOTOPICALLY_TRIVIAL_ON_COMPONENTS_NULL = `!s:real^M->bool t:real^N->bool.
        (locally connected s \/ compact s /\ ANR t) /\ path_connected t
         ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET t
                   ==> ?a. homotopic_with (\x. T)
                            (subtopology euclidean s,
                             subtopology euclidean t) f (\x. a)) <=>
              (!c. c IN components s
                   ==> (!f. f continuous_on c /\ IMAGE f c SUBSET t
                            ==> ?a. homotopic_with (\x. T)
                                     (subtopology euclidean c,
                                      subtopology euclidean t) f (\x. a))))`;;

let COHOMOTOPICALLY_TRIVIAL_1D = `!f:real^M->real^N s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        ANR t /\ connected t /\
        (dimindex(:M) = 1 \/ ?r:real^1->bool. s homeomorphic r)
        ==> ?a. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean t) f (\x. a)`;;

(* ------------------------------------------------------------------------- *)
(* A few simple lemmas about deformation retracts.                           *)
(* ------------------------------------------------------------------------- *)

let DEFORMATION_RETRACTION_COMPOSE = `!s t u r1 r2:real^N->real^N.
        homotopic_with (\x. T)
          (subtopology euclidean s,subtopology euclidean s) (\x. x) r1 /\
        retraction (s,t) r1 /\
        homotopic_with (\x. T)
          (subtopology euclidean t,subtopology euclidean t) (\x. x) r2 /\
        retraction (t,u) r2
        ==> homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean s)
             (\x. x) (r2 o r1) /\
            retraction (s,u) (r2 o r1)`;;

let DEFORMATION_RETRACT_TRANS = `!s t u:real^N->bool.
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction (s,t) r) /\
        (?r. homotopic_with (\x. T)
              (subtopology euclidean t,subtopology euclidean t) (\x. x) r /\
             retraction (t,u) r)
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction (s,u) r`;;

let DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT = `!s t:real^N->bool.
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction(s,t) r)
        ==> s homotopy_equivalent t`;;

let DEFORMATION_RETRACT = `!s t:real^N->bool.
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction(s,t) r) <=>
        t retract_of s /\
        ?f. homotopic_with (\x. T)
             (subtopology euclidean s,subtopology euclidean s) (\x. x) f /\
            IMAGE f s SUBSET t`;;

let ANR_STRONG_DEFORMATION_RETRACTION = `!s t:real^N->bool.
        ANR s /\
        (?r. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
             retraction(s,t) r)
        ==> ?r. homotopic_with (\h. !x. x IN t ==> h x = x)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`;;

let DEFORMATION_RETRACT_OF_CONTRACTIBLE = `!s t:real^N->bool.
        contractible s /\ t retract_of s
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`;;

let AR_DEFORMATION_RETRACT_OF_CONTRACTIBLE = `!s t:real^N->bool.
        contractible s /\ AR t /\ closed_in (subtopology euclidean s) t
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`;;

let DEFORMATION_RETRACT_OF_CONTRACTIBLE_SING = `!s a:real^N.
        contractible s /\ a IN s
        ==> ?r. homotopic_with (\x. T)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,{a}) r`;;

let STRONG_DEFORMATION_RETRACT_OF_AR = `!s t:real^N->bool.
        AR s /\ t retract_of s
        ==> ?r. homotopic_with (\h. !x. x IN t ==> h x = x)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`;;

let AR_STRONG_DEFORMATION_RETRACT_OF_AR = `!s t:real^N->bool.
        AR s /\ AR t /\ closed_in (subtopology euclidean s) t
        ==> ?r. homotopic_with (\h. !x. x IN t ==> h x = x)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,t) r`;;

let SING_STRONG_DEFORMATION_RETRACT_OF_AR = `!s a:real^N.
        AR s /\ a IN s
        ==> ?r. homotopic_with (\h. h a = a)
                 (subtopology euclidean s,subtopology euclidean s) (\x. x) r /\
                retraction(s,{a}) r`;;

let HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_CONVEX = `!s t a:real^N.
      convex s /\ bounded s /\ a IN relative_interior s /\
      convex t /\ relative_frontier s SUBSET t /\ t SUBSET affine hull s
      ==> (relative_frontier s) homotopy_equivalent (t DELETE a)`;;

let HOMOTOPY_EQUIVALENT_RELATIVE_FRONTIER_PUNCTURED_AFFINE_HULL = `!s a:real^N.
      convex s /\ bounded s /\ a IN relative_interior s
      ==> (relative_frontier s) homotopy_equivalent (affine hull s DELETE a)`;;

let HOMOTOPY_EQUIVALENT_PUNCTURED_UNIV_SPHERE = `!c a:real^N r.
        &0 < r ==> ((:real^N) DELETE c) homotopy_equivalent sphere(a,r)`;;

(* ------------------------------------------------------------------------- *)
(* Preservation of fixpoints under (more general notion of) retraction.      *)
(* ------------------------------------------------------------------------- *)

let INVERTIBLE_FIXPOINT_PROPERTY = `!s:real^M->bool t:real^N->bool i r.
     i continuous_on t /\ IMAGE i t SUBSET s /\
     r continuous_on s /\ IMAGE r s SUBSET t /\
     (!y. y IN t ==> (r(i(y)) = y))
     ==> (!f. f continuous_on s /\ IMAGE f s SUBSET s
              ==> ?x. x IN s /\ (f x = x))
         ==> !g. g continuous_on t /\ IMAGE g t SUBSET t
                 ==> ?y. y IN t /\ (g y = y)`;;

let HOMEOMORPHIC_FIXPOINT_PROPERTY = `!s t. s homeomorphic t
         ==> ((!f. f continuous_on s /\ IMAGE f s SUBSET s
                   ==> ?x. x IN s /\ (f x = x)) <=>
              (!g. g continuous_on t /\ IMAGE g t SUBSET t
                   ==> ?y. y IN t /\ (g y = y)))`;;

let RETRACT_FIXPOINT_PROPERTY = `!s t:real^N->bool.
        t retract_of s /\
        (!f. f continuous_on s /\ IMAGE f s SUBSET s
             ==> ?x. x IN s /\ (f x = x))
        ==> !g. g continuous_on t /\ IMAGE g t SUBSET t
                ==> ?y. y IN t /\ (g y = y)`;;

let FRONTIER_SUBSET_RETRACTION = `!s:real^N->bool t r.
        bounded s /\
        frontier s SUBSET t /\
        r continuous_on (closure s) /\
        IMAGE r s SUBSET t /\
        (!x. x IN t ==> r x = x)
        ==> s SUBSET t`;;

let NO_RETRACTION_FRONTIER_BOUNDED = `!s:real^N->bool.
        bounded s /\ ~(interior s = {}) ==> ~((frontier s) retract_of s)`;;

let COMPACT_SUBSET_FRONTIER_RETRACTION = `!f:real^N->real^N s.
        compact s /\ f continuous_on s /\ (!x. x IN frontier s ==> f x = x)
        ==> s SUBSET IMAGE f s`;;

let NOT_ABSOLUTE_RETRACT_COBOUNDED = `!s. bounded s /\ ((:real^N) DIFF s) retract_of (:real^N) ==> s = {}`;;

(* ------------------------------------------------------------------------- *)
(* Bohl-type fixed point theorems.                                           *)
(* ------------------------------------------------------------------------- *)

let BOHL = `!f s a:real^N.
        f continuous_on s /\ convex s /\ compact s /\ a IN interior s
        ==> (?x. x IN s /\ f x = x) \/
            (?x. x IN frontier s /\ x IN segment(a,f x))`;;

let BOHL_ALT = `!f s a.
        f continuous_on s /\ convex s /\ compact s /\ a IN interior s /\
        IMAGE f s SUBSET (:real^N) DELETE a
        ==> ?x. x IN frontier s /\ a IN segment(x,f x)`;;

let BOHL_SIMPLE = `!f:real^N->real^N s a.
       compact s /\ a IN s /\
       f continuous_on s /\ IMAGE f s SUBSET (:real^N) DELETE a
       ==> ?x. x IN frontier s /\ ~(f x = x)`;;

(* ------------------------------------------------------------------------- *)
(* Some more theorems about connectivity of retract complements.             *)
(* ------------------------------------------------------------------------- *)

let BOUNDED_COMPONENT_RETRACT_COMPLEMENT_MEETS = `!s t c. closed s /\ s retract_of t /\
           c IN components((:real^N) DIFF s) /\ bounded c
           ==> ~(c SUBSET t)`;;

let COMPONENT_RETRACT_COMPLEMENT_MEETS = `!s t c. closed s /\ s retract_of t /\ bounded t /\
           c IN components((:real^N) DIFF s)
           ==> ~(c SUBSET t)`;;

let FINITE_COMPLEMENT_ENR_COMPONENTS = `!s. compact s /\ ENR s ==> FINITE(components((:real^N) DIFF s))`;;

let FINITE_COMPLEMENT_ANR_COMPONENTS = `!s. compact s /\ ANR s ==> FINITE(components((:real^N) DIFF s))`;;

let CARD_LE_RETRACT_COMPLEMENT_COMPONENTS = `!s t. compact s /\ s retract_of t /\ bounded t
         ==> components((:real^N) DIFF s) <=_c components((:real^N) DIFF t)`;;

let CONNECTED_RETRACT_COMPLEMENT = `!s t. compact s /\ s retract_of t /\ bounded t /\
         connected((:real^N) DIFF t)
         ==> connected((:real^N) DIFF s)`;;

(* ------------------------------------------------------------------------- *)
(* We also get fixpoint properties for suitable ANRs.                        *)
(* ------------------------------------------------------------------------- *)

let BROUWER_INESSENTIAL_ANR = `!f:real^N->real^N s.
        compact s /\ ~(s = {}) /\ ANR s /\
        f continuous_on s /\ IMAGE f s SUBSET s /\
        (?a. homotopic_with (\x. T)
              (subtopology euclidean s,subtopology euclidean s) f (\x. a))
        ==> ?x. x IN s /\ f x = x`;;

let BROUWER_CONTRACTIBLE_ANR = `!f:real^N->real^N s.
        compact s /\ contractible s /\ ~(s = {}) /\ ANR s /\
        f continuous_on s /\ IMAGE f s SUBSET s
        ==> ?x. x IN s /\ f x = x`;;

let FIXED_POINT_INESSENTIAL_SPHERE_MAP = `!f a:real^N r c.
     &0 < r /\
     homotopic_with (\x. T)
      (subtopology euclidean (sphere(a,r)),
       subtopology euclidean (sphere(a,r))) f (\x. c)
     ==> ?x. x IN sphere(a,r) /\ f x = x`;;

let BROUWER_AR = `!f s:real^N->bool.
        compact s /\ AR s /\ f continuous_on s /\ IMAGE f s SUBSET s
         ==> ?x. x IN s /\ f x = x`;;

let BROUWER_ABSOLUTE_RETRACT = `!f s. compact s /\ s retract_of (:real^N) /\
         f continuous_on s /\ IMAGE f s SUBSET s
         ==> ?x. x IN s /\ f x = x`;;

(* ------------------------------------------------------------------------- *)
(* This interesting lemma is no longer used for Schauder but we keep it.     *)
(* ------------------------------------------------------------------------- *)

let SCHAUDER_PROJECTION = `!s:real^N->bool e.
        compact s /\ &0 < e
        ==> ?t f. FINITE t /\ t SUBSET s /\
                  f continuous_on s /\ IMAGE f s SUBSET (convex hull t) /\
                  (!x. x IN s ==> norm(f x - x) < e)`;;

(* ------------------------------------------------------------------------- *)
(* Some other related fixed-point theorems.                                  *)
(* ------------------------------------------------------------------------- *)

let BROUWER_FACTOR_THROUGH_AR = `!f:real^M->real^N g:real^N->real^M s t.
        f continuous_on s /\ IMAGE f s SUBSET t /\
        g continuous_on t /\ IMAGE g t SUBSET s /\
        compact s /\ AR t
        ==> ?x. x IN s /\ g(f x) = x`;;

let BROUWER_ABSOLUTE_RETRACT_GEN = `!f s:real^N->bool.
           s retract_of (:real^N) /\
           f continuous_on s /\ IMAGE f s SUBSET s /\ bounded(IMAGE f s)
           ==> ?x. x IN s /\ f x = x`;;

let SCHAUDER_GEN = `!f s t:real^N->bool.
     AR s /\ f continuous_on s /\ IMAGE f s SUBSET t /\ t SUBSET s /\ compact t
     ==> ?x. x IN t /\ f x = x`;;

let SCHAUDER = `!f s t:real^N->bool.
        convex s /\ ~(s = {}) /\ t SUBSET s /\ compact t /\
        f continuous_on s /\ IMAGE f s SUBSET t
        ==> ?x. x IN s /\ f x = x`;;

let SCHAUDER_UNIV = `!f:real^N->real^N.
        f continuous_on (:real^N) /\ bounded (IMAGE f (:real^N))
        ==> ?x. f x = x`;;

let ROTHE = `!f s:real^N->bool.
        closed s /\ convex s /\ ~(s = {}) /\
        f continuous_on s /\ bounded(IMAGE f s) /\
        IMAGE f (frontier s) SUBSET s
        ==> ?x. x IN s /\ f x = x`;;

(* ------------------------------------------------------------------------- *)
(* Perron-Frobenius theorem.                                                 *)
(* ------------------------------------------------------------------------- *)

let PERRON_FROBENIUS = `!A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
               ==> &0 <= A$i$j)
        ==> ?v c. norm v = &1 /\ &0 <= c /\ A ** v = c % v`;;

(* ------------------------------------------------------------------------- *)
(* Bijections between intervals.                                             *)
(* ------------------------------------------------------------------------- *)

let interval_bij = new_definition
 `interval_bij (a:real^N,b:real^N) (u:real^N,v:real^N) (x:real^N) =
    (lambda i. u$i + (x$i - a$i) / (b$i - a$i) * (v$i - u$i)):real^N`;;

let INTERVAL_BIJ_AFFINE = `interval_bij (a,b) (u,v) =
        \x. (lambda i. (v$i - u$i) / (b$i - a$i) * x$i) +
            (lambda i. u$i - (v$i - u$i) / (b$i - a$i) * a$i)`;;

let CONTINUOUS_INTERVAL_BIJ = `!a b u v x. (interval_bij (a:real^N,b:real^N) (u:real^N,v:real^N))
                  continuous at x`;;

let CONTINUOUS_ON_INTERVAL_BIJ = `!a b u v s. interval_bij (a,b) (u,v) continuous_on s`;;

let IN_INTERVAL_INTERVAL_BIJ = `!a b u v x:real^N.
        x IN interval[a,b] /\ ~(interval[u,v] = {})
        ==> (interval_bij (a,b) (u,v) x) IN interval[u,v]`;;

let INTERVAL_BIJ_BIJ = `!a b u v x:real^N.
        (!i. 1 <= i /\ i <= dimindex(:N) ==> a$i < b$i /\ u$i < v$i)
        ==> interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x`;;

(* ------------------------------------------------------------------------- *)
(* Fashoda meet theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let INFNORM_2 = `infnorm (x:real^2) = max (abs(x$1)) (abs(x$2))`;;

let INFNORM_EQ_1_2 = `infnorm (x:real^2) = &1 <=>
        abs(x$1) <= &1 /\ abs(x$2) <= &1 /\
        (x$1 = -- &1 \/ x$1 = &1 \/ x$2 = -- &1 \/ x$2 = &1)`;;

let INFNORM_EQ_1_IMP = `infnorm (x:real^2) = &1 ==> abs(x$1) <= &1 /\ abs(x$2) <= &1`;;

let FASHODA_UNIT = `!f:real^1->real^2 g:real^1->real^2.
        IMAGE f (interval[--vec 1,vec 1]) SUBSET interval[--vec 1,vec 1] /\
        IMAGE g (interval[--vec 1,vec 1]) SUBSET interval[--vec 1,vec 1] /\
        f continuous_on interval[--vec 1,vec 1] /\
        g continuous_on interval[--vec 1,vec 1] /\
        f(--vec 1)$1 = -- &1 /\ f(vec 1)$1 = &1 /\
        g(--vec 1)$2 = -- &1 /\ g(vec 1)$2 = &1
        ==> ?s t. s IN interval[--vec 1,vec 1] /\
                  t IN interval[--vec 1,vec 1] /\
                  f(s) = g(t)`;;

let FASHODA_UNIT_PATH = `!f:real^1->real^2 g:real^1->real^2.
        path f /\ path g /\
        path_image f SUBSET interval[--vec 1,vec 1] /\
        path_image g SUBSET interval[--vec 1,vec 1] /\
        (pathstart f)$1 = -- &1 /\ (pathfinish f)$1 = &1 /\
        (pathstart g)$2 = -- &1 /\ (pathfinish g)$2 = &1
        ==> ?z. z IN path_image f /\ z IN path_image g`;;

let FASHODA = `!f g a b:real^2.
        path f /\ path g /\
        path_image f SUBSET interval[a,b] /\
        path_image g SUBSET interval[a,b] /\
        (pathstart f)$1 = a$1 /\ (pathfinish f)$1 = b$1 /\
        (pathstart g)$2 = a$2 /\ (pathfinish g)$2 = b$2
        ==> ?z. z IN path_image f /\ z IN path_image g`;;

(* ------------------------------------------------------------------------- *)
(* Some slightly ad hoc lemmas I use below                                   *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_VERTICAL = `!a:real^2 b:real^2 x:real^2.
      a$1 = b$1
      ==> (x IN segment[a,b] <=>
           x$1 = a$1 /\ x$1 = b$1 /\
           (a$2 <= x$2 /\ x$2 <= b$2 \/ b$2 <= x$2 /\ x$2 <= a$2))`;;

let SEGMENT_HORIZONTAL = `!a:real^2 b:real^2 x:real^2.
      a$2 = b$2
      ==> (x IN segment[a,b] <=>
           x$2 = a$2 /\ x$2 = b$2 /\
           (a$1 <= x$1 /\ x$1 <= b$1 \/ b$1 <= x$1 /\ x$1 <= a$1))`;;

(* ------------------------------------------------------------------------- *)
(* Useful Fashoda corollary pointed out to me by Tom Hales.                  *)
(* ------------------------------------------------------------------------- *)

let FASHODA_INTERLACE = `!f g a b:real^2.
        path f /\ path g /\
        path_image f SUBSET interval[a,b] /\
        path_image g SUBSET interval[a,b] /\
        (pathstart f)$2 = a$2 /\ (pathfinish f)$2 = a$2 /\
        (pathstart g)$2 = a$2 /\ (pathfinish g)$2 = a$2 /\
        (pathstart f)$1 < (pathstart g)$1 /\
        (pathstart g)$1 < (pathfinish f)$1 /\
        (pathfinish f)$1 < (pathfinish g)$1
        ==> ?z. z IN path_image f /\ z IN path_image g`;;

(* ------------------------------------------------------------------------- *)
(* Complement in dimension N >= 2 of set homeomorphic to any interval in     *)
(* any dimension is (path-)connected. This naively generalizes the argument  *)
(* in Ryuji Maehara's paper "The Jordan curve theorem via the Brouwer        *)
(* fixed point theorem", American Mathematical Monthly 1984.                 *)
(* ------------------------------------------------------------------------- *)

let UNBOUNDED_COMPONENTS_COMPLEMENT_ABSOLUTE_RETRACT = `!s c. compact s /\ AR s /\ c IN components((:real^N) DIFF s)
         ==> ~bounded c`;;

let CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT = `!s. 2 <= dimindex(:N) /\ compact s /\ AR s
       ==> connected((:real^N) DIFF s)`;;

let PATH_CONNECTED_COMPLEMENT_ABSOLUTE_RETRACT = `!s:real^N->bool.
        2 <= dimindex(:N) /\ compact s /\ AR s
        ==> path_connected((:real^N) DIFF s)`;;

let CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT = `!s:real^N->bool t:real^M->bool.
        2 <= dimindex(:N) /\ s homeomorphic t /\ convex t /\ compact t
        ==> connected((:real^N) DIFF s)`;;

let PATH_CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT = `!s:real^N->bool t:real^M->bool.
        2 <= dimindex(:N) /\ s homeomorphic t /\ convex t /\ compact t
        ==> path_connected((:real^N) DIFF s)`;;

(* ------------------------------------------------------------------------- *)
(* In particular, apply all these to the special case of an arc.             *)
(* ------------------------------------------------------------------------- *)

let RETRACTION_ARC = `!p. arc p
       ==> ?f. f continuous_on (:real^N) /\
               IMAGE f (:real^N) SUBSET path_image p /\
               (!x. x IN path_image p ==> f x = x)`;;

let PATH_CONNECTED_ARC_COMPLEMENT = `!p. 2 <= dimindex(:N) /\ arc p
       ==> path_connected((:real^N) DIFF path_image p)`;;

let CONNECTED_ARC_COMPLEMENT = `!p. 2 <= dimindex(:N) /\ arc p
       ==> connected((:real^N) DIFF path_image p)`;;

let INSIDE_ARC_EMPTY = `!p:real^1->real^N. arc p ==> inside(path_image p) = {}`;;

let INSIDE_SIMPLE_CURVE_IMP_CLOSED = `!g x:real^N.
        simple_path g /\ x IN inside(path_image g)
        ==> pathfinish g = pathstart g`;;

(* ------------------------------------------------------------------------- *)
(* Some nice theorems giving accessibility for ANR complement components     *)
(* (from Hu's "Theory of Retracts", apparently originally from Borsuk).      *)
(* ------------------------------------------------------------------------- *)

let FINITE_ANR_COMPLEMENT_COMPONENTS_CONCENTRIC = `!s p:real^N a b.
        compact s /\ ANR s /\ a < b
        ==> FINITE {c | c IN components(cball(p,b) DIFF s) /\
                        ~(closure c INTER cball(p,a) = {})}`;;

let ACCESSIBLE_FRONTIER_ANR_INTER_COMPLEMENT_COMPONENT = `!s c p:real^N b.
        compact s /\ ANR s /\
        c IN components(b DIFF s) /\ p IN frontier c /\ p IN interior b
        ==> ?g. arc g /\ pathfinish g = p /\
                !t. t IN interval[vec 0,vec 1] DELETE (vec 1) ==> g(t) IN c`;;

let ACCESSIBLE_FRONTIER_ANR_COMPLEMENT_COMPONENT = `!s c x y.
        compact s /\ ANR s /\
        c IN components((:real^N) DIFF s) /\ x IN c /\ y IN frontier c
        ==> ?g. arc g /\ pathstart g = x /\ pathfinish g = y /\
                !t. t IN interval[vec 0,vec 1] DELETE (vec 1) ==> g(t) IN c`;;

(* ------------------------------------------------------------------------- *)
(* Some simple consequences for complement connectivity.                     *)
(* ------------------------------------------------------------------------- *)

let LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT = `!s c t.
        compact s /\
        ANR s /\
        c IN components ((:real^N) DIFF s) /\
        c SUBSET t /\
        t SUBSET closure c
        ==> locally path_connected t`;;

let LPC_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT = `!s t. compact s /\ ANR s /\
         (:real^N) DIFF s SUBSET t /\ DISJOINT t (interior s)
         ==> locally path_connected t`;;

let LPC_SUPERSET_COMPLEMENT_SIMPLE_PATH_IMAGE = `!g s:real^N->bool.
        2 <= dimindex(:N) /\ simple_path g /\
        (:real^N) DIFF path_image g SUBSET s
        ==> locally path_connected s`;;

let LPC_OPEN_SIMPLE_PATH_COMPLEMENT = `!g. simple_path g
       ==> locally path_connected
            ((:real^N) DIFF (path_image g DIFF {pathstart g,pathfinish g}))`;;

let PATH_CONNECTED_INTERMEDIATE_CLOSURE_ANR_COMPLEMENT_COMPONENT = `!s c t.
        compact s /\ ANR s /\ c IN components((:real^N) DIFF s) /\
        c SUBSET t /\ t SUBSET closure c
        ==> path_connected t`;;

let PATH_CONNECTED_SUPERSET_COMPLEMENT_ARC_IMAGE = `!g s:real^N->bool.
        2 <= dimindex(:N) /\ arc g /\ (:real^N) DIFF path_image g SUBSET s
        ==> path_connected s`;;

let PATH_CONNECTED_OPEN_ARC_COMPLEMENT = `!g. 2 <= dimindex(:N) /\ arc g
       ==> path_connected
            ((:real^N) DIFF (path_image g DIFF {pathstart g,pathfinish g}))`;;
