(* ========================================================================= *)
(* Impossibility of cube dissection into finitely many smaller cubes of      *)
(* pairwise distinct sizes ("cubing the cube"), originally proved by         *)
(* R. L. Brooks, C. A. B. Smith, A. H. Stone and W. T. Tutte,                *)
(* "The Dissection of Rectangles into Squares",                              *)
(* Duke Mathematical Journal, vol. 7 (1940), pp. 312-340.                    *)
(*                                                                           *)
(* The proof follows the elegant argument presented in J. E. Littlewood,     *)
(* "A Mathematician's Miscellany" (CUP, 1953), revised edition               *)
(* "Littlewood's Miscellany" (ed. B. Bollobas, CUP, 1986), pp. 28-29.        *)
(*                                                                           *)
(* Formalized in HOL Light by Claude Code (Opus 4.6), February 2026.         *)
(* ========================================================================= *)

needs "Multivariate/integration.ml";;

(* ------------------------------------------------------------------------- *)
(* Cube-shaped boxes in R^N (we only really use it for R^3 here)             *)
(* ------------------------------------------------------------------------- *)

let cube = new_definition
 `cube k <=>
     ?a:real^N d. &0 < d /\ k = interval[a,a + d % vec 1]`;;

let CUBE_IMP_NONEMPTY_INTERIOR = `!k:real^N->bool. cube k ==> ~(interior k = {})`;;

let CUBE_IMP_NONEMPTY = `!k:real^N->bool. cube k ==> ~(k = {})`;;

(* ------------------------------------------------------------------------- *)
(* The length of an interval (first component; we only use it for cubes).    *)
(* ------------------------------------------------------------------------- *)

let interval_length = new_definition
 `interval_length (s:real^N->bool) =
        if s = {} then &0
        else interval_upperbound s$1 - interval_lowerbound s$1`;;

let INTERVAL_LENGTH_CUBE = `!(a:real^N) d. interval_length(interval[a,a + d % vec 1]) = max d (&0)`;;

let INTERVAL_LENGTH_CUBE_COMPONENT = `!(k:real^N->bool) i.
        cube k
        ==> interval_upperbound k$i - interval_lowerbound k$i =
            interval_length k`;;

let INTERVAL_LENGTH_CUBE_POS = `!(a:real^N) d. &0 < d ==> interval_length(interval[a, a + d % vec 1]) = d`;;

let VECTOR2_CUBE = `!c:real^3 s. vector[c$2 + s; c$3 + s]:real^2 =
                vector[c$2; c$3] + s % vec 1`;;

let CUBE_BOUNDS_TAC =
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND; INTERVAL_UPPERBOUND;
    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
    REAL_MUL_RID; REAL_LE_ADDR; REAL_LT_IMP_LE];;

let MESON_ASSUME_TAC lemmas tm =
  SUBGOAL_THEN tm ASSUME_TAC THENL [ASM_MESON_TAC lemmas; ALL_TAC];;

(* ------------------------------------------------------------------------- *)
(* Dissection of a set into pairwise differently-sized nonempty cubes.       *)
(* ------------------------------------------------------------------------- *)

let cube_dissection = new_definition
 `cube_dissection (d:(real^N->bool)->bool) <=>
        d division_of UNIONS d /\
        (!k. k IN d ==> cube k) /\
        pairwise (\k k'. ~(interval_length k = interval_length k')) d`;;

(* ------------------------------------------------------------------------- *)
(* A point on the boundary of a division element must belong to another.     *)
(* ------------------------------------------------------------------------- *)

let POINT_IN_MULTIPLE_DIVISION_OF_GEN = `!D a b u v (x:real^N) i.
        D division_of UNIONS D /\
        interval[u,v] IN D /\ x IN interval[u,v] /\
        interval[a,b] SUBSET UNIONS D /\
        interval[u,v] SUBSET interval[a,b] /\
        1 <= i /\ i <= dimindex(:N) /\
        a$i < x$i /\ x$i < b$i /\ (x$i = u$i \/ x$i = v$i)
        ==> ?j'. j' IN D /\ ~(j' = interval[u,v]) /\ x IN j'`;;

(* Specialized version when D division_of interval[a,b] *)
let POINT_IN_MULTIPLE_DIVISION_OF = `!D a b u v (x:real^N) i.
        D division_of interval[a,b] /\
        interval[u,v] IN D /\ x IN interval[u,v] /\
        1 <= i /\ i <= dimindex(:N) /\
        a$i < x$i /\ x$i < b$i /\ (x$i = u$i \/ x$i = v$i)
        ==> ?j'. j' IN D /\ ~(j' = interval[u,v]) /\ x IN j'`;;

let CUBE_EXISTS_FORM = `!D:(real^N->bool)->bool.
        cube_dissection D /\
        (!(x:real^N) e. interval[x,x + e % vec 1] IN D /\
               P(interval[x,x + e % vec 1])
               ==> R x e)
        ==> (?j. j IN D /\ P j) ==> (?(x:real^N) e. R x e)`;;

let SQUARE_DISSECTION_NONEDGE = `!D a b j:real^2->bool.
        cube_dissection D /\ UNIONS D = interval[a,b] /\ j IN D /\
        (!j'. j' IN D /\ ~(j' = j)
             ==> interval_length(j) < interval_length j')
        ==> j = interval[a,b] \/ j SUBSET interval(a,b)`;;

(* Minimum element of a finite set with pairwise distinct f-values *)
let FINITE_PAIRWISE_MINIMUM = `!(f:A->real) s.
    FINITE s /\ ~(s = {}) /\ pairwise (\x y. ~(f x = f y)) s
    ==> ?x. x IN s /\ !y. y IN s /\ ~(y = x) ==> f x < f y`;;

(* =================================================================== *)
(* Valley-based proof of cube dissection impossibility                 *)
(* Following the infinite descent approach of Brooks/Smith/Stone/Tutte *)
(* =================================================================== *)

(* A valley for a dissection D is a cube v whose "top face" is        *)
(* properly covered by cubes from D. The cubes sitting on v have      *)
(* their footprint within v's and are strictly smaller than v.        *)

let valley = new_definition
 `valley (D:(real^3->bool)->bool) (v:real^3->bool) <=>
    cube v /\
    (!z:real^3. z$1 = interval_upperbound (v:real^3->bool) $ 1 /\
                interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
                z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
                interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
                z$3 < interval_upperbound (v:real^3->bool) $ 3
                ==> ?k. k IN D /\ z IN k /\
                        interval_lowerbound k $ 1 =
                        interval_upperbound (v:real^3->bool) $ 1) /\
    (!k. k IN D /\
         interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
         (?z:real^3. z IN k /\
              interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
              z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
              interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
              z$3 < interval_upperbound (v:real^3->bool) $ 3)
         ==> interval_lowerbound (v:real^3->bool) $ 2 <= interval_lowerbound k $ 2 /\
             interval_upperbound k $ 2 <= interval_upperbound (v:real^3->bool) $ 2 /\
             interval_lowerbound (v:real^3->bool) $ 3 <= interval_lowerbound k $ 3 /\
             interval_upperbound k $ 3 <= interval_upperbound (v:real^3->bool) $ 3) /\
    (!k. k IN D /\
         interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
         (?z:real^3. z IN k /\
              interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
              z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
              interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
              z$3 < interval_upperbound (v:real^3->bool) $ 3)
         ==> interval_length k < interval_length v)`;;

(* The initial valley: the bottom face of [a,b] is a valley.         *)
(* More precisely, the cube shifted down below [a,b] is a valley.    *)

let DIVISION_WHOLE_IS_SINGLETON = `!D (a:real^3) b.
    D division_of interval[a,b] /\
    (!k:real^3->bool. k IN D ==> cube k) /\
    interval[a,b] IN D
    ==> D = {interval[a,b]}`;;

let VALLEY_INITIAL = `!D (a:real^3) d.
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    ~(D = {interval[a, a + d % vec 1]})
    ==> valley D (interval[a - d % basis 1, a - d % basis 1 + d % vec 1])`;;

(* If x is on k's face at coordinate 1 (x$1 = upperbound k$1) with    *)
(* interior y,z in k, and j is a different element of a division       *)
(* containing x, then j starts exactly at k's upper x-bound.           *)

let DIVISION_FACE_LOWERBOUND = `!D (k:real^3->bool) j (x:real^3).
    D division_of UNIONS D /\
    ~(interior k = {}) /\ ~(interior j = {}) /\
    k IN D /\ j IN D /\ ~(j = k) /\
    x IN k /\ x IN j /\
    x$1 = interval_upperbound k $ 1 /\
    interval_lowerbound k $ 2 < x$2 /\
    x$2 < interval_upperbound k $ 2 /\
    interval_lowerbound k $ 3 < x$3 /\
    x$3 < interval_upperbound k $ 3
    ==> interval_lowerbound j $ 1 = interval_upperbound k $ 1`;;

(* Shared setup for pairs of elements from the 2D face-projection set E. *)
(* Expands e1,e2 from E, gets 3D preimages m1,m2, proves m1!=m2,        *)
(* extracts cube forms and interval bounds.                            *)
let E_PAIR_PREIMAGE_TAC =
  UNDISCH_TAC `(e1:real^2->bool) IN E` THEN
  EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m1:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(e2:real^2->bool) IN E` THEN
  EXPAND_TAC "E" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m2:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(m1:real^3->bool = m2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(e1:real^2->bool = e2)` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(?c1:real^3 s1. &0 < s1 /\ m1 = interval[c1, c1 + s1 % vec 1]) /\
     (?c2:real^3 s2. &0 < s2 /\ m2 = interval[c2, c2 + s2 % vec 1])` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN ASM_MESON_TAC[cube_dissection; cube]; ALL_TAC] THEN
  SUBGOAL_THEN `interval_lowerbound m1 = c1:real^3 /\
     interval_upperbound m1 = c1 + s1 % vec 1:real^3 /\
     interval_lowerbound m2 = c2:real^3 /\
     interval_upperbound m2 = c2 + s2 % vec 1:real^3` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN CUBE_BOUNDS_TAC; ALL_TAC];;

(* The smallest cube on v's face is strictly in v's y,z interior,      *)
(* not touching v's face boundary. This is essential for the wall      *)
(* argument: it ensures wall cubes exist on all sides of k.            *)
(* Proof uses 2D projection onto v's face + SQUARE_DISSECTION_NONEDGE *)

let VALLEY_FACE_INTERIOR = `!D (a:real^3) d (v:real^3->bool) k.
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v /\
    k IN D /\
    interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
    (?z:real^3. z IN k /\
         interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\ z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
         interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\ z$3 < interval_upperbound (v:real^3->bool) $ 3) /\
    (!j'. j' IN D /\ ~(j' = k) /\
          interval_lowerbound j' $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
          (?z:real^3. z IN j' /\
               interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
               z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
               interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
               z$3 < interval_upperbound (v:real^3->bool) $ 3)
          ==> interval_length k < interval_length j')
    ==> interval_lowerbound (v:real^3->bool) $ 2 < interval_lowerbound k $ 2 /\
        interval_upperbound k $ 2 < interval_upperbound (v:real^3->bool) $ 2 /\
        interval_lowerbound (v:real^3->bool) $ 3 < interval_lowerbound k $ 3 /\
        interval_upperbound k $ 3 < interval_upperbound (v:real^3->bool) $ 3`;;

(* Helper: a nonempty open real interval minus a finite set is nonempty *)
let REAL_OPEN_INTERVAL_AVOID_FINITE = `!s a b. FINITE s /\ a < b ==> ?x:real. a < x /\ x < b /\ ~(x IN s)`;;

(* Containment: if k is the smallest on v's face, and j starts at k's  *)
(* right face with a point in k's y,z interior, and m is an adjacent   *)
(* cube on v's face forming a "wall", then j fits inside k.            *)

(* Get a real w2 (resp. w3) in an open interval (lo,hi) avoiding all  *)
(* cube lowerbound/upperbound values in dimension 2 (resp. 3).       *)
let AVOID_DIM2_TAC lo hi =
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` lo hi) ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MAX_LT; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\k':real^3->bool. interval_lowerbound k' $ 2) D UNION
    IMAGE (\k':real^3->bool. interval_upperbound k' $ 2) D`; lo; hi]
   REAL_OPEN_INTERVAL_AVOID_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real` STRIP_ASSUME_TAC);;

let AVOID_DIM3_TAC lo hi =
  SUBGOAL_THEN (mk_binop `(<):real->real->bool` lo hi) ASSUME_TAC THENL
   [REWRITE_TAC[REAL_MAX_LT; REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\k':real^3->bool. interval_lowerbound k' $ 3) D UNION
    IMAGE (\k':real^3->bool. interval_upperbound k' $ 3) D`; lo; hi]
   REAL_OPEN_INTERVAL_AVOID_FINITE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w3:real` STRIP_ASSUME_TAC);;

(* Common tactic for the 4 bound branches of VALLEY_DESCENT_CONTAINMENT *)
(* Given: valley v, witness vector[ub v$1; w2; w3] in face,
   w2/w3 avoiding cube boundaries, various bounds on w2/w3 *)
(* Proves: contradiction via interior overlap with j *)
let BOUND_COMMON_TAC =
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [valley]) THEN DISCH_THEN(MP_TAC o SPEC
    `vector[interval_upperbound (v:real^3->bool) $ 1; w2; w3]:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* m != k: the witness point is outside k by choice of w2 or w3 *)
  SUBGOAL_THEN `~(m = k:real^3->bool)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC
      `(vector[interval_upperbound (v:real^3->bool) $ 1; w2; w3]:real^3) IN
        (k:real^3->bool)` THEN
    ASM_REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID; VECTOR_3] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* m cube *)
  MESON_ASSUME_TAC [cube_dissection] `cube(m:real^3->bool)` THEN
  SUBGOAL_THEN `?cm:real^3 sm. &0 < sm /\ m = interval[cm, cm + sm % vec 1]`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[cube]; ALL_TAC] THEN
  SUBGOAL_THEN `(cm + sm % vec 1:real^3)$2 = cm$2 + sm /\
     (cm + sm % vec 1:real^3)$3 = cm$3 + sm` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `interval_lowerbound m = (cm:real^3) /\
     interval_upperbound m = cm + sm % vec 1:real^3` STRIP_ASSUME_TAC THENL
   [CUBE_BOUNDS_TAC; ALL_TAC] THEN
  (* interval_length k < interval_length m *)
  SUBGOAL_THEN `interval_length (k:real^3->bool) < interval_length (m:real^3->bool)`
    ASSUME_TAC THENL [SUBGOAL_THEN
      `m IN D /\ ~(m = k:real^3->bool) /\
       interval_lowerbound (m:real^3->bool) $ 1 =
         interval_upperbound (v:real^3->bool) $ 1 /\
       (?zz:real^3. zz IN m /\
         interval_lowerbound (v:real^3->bool) $ 2 < zz$2 /\
         zz$2 < interval_upperbound (v:real^3->bool) $ 2 /\
         interval_lowerbound (v:real^3->bool) $ 3 < zz$3 /\
         zz$3 < interval_upperbound (v:real^3->bool) $ 3)`
      MP_TAC THENL [ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `vector[interval_upperbound (v:real^3->bool) $ 1;
                w2; w3]:real^3` THEN ASM_REWRITE_TAC[VECTOR_3]; ALL_TAC] THEN
    ASM_MESON_TAC[]; ALL_TAC] THEN
  (* sk < sm *)
  SUBGOAL_THEN `sk < sm` ASSUME_TAC THENL [UNDISCH_TAC
      `interval_length (k:real^3->bool) < interval_length (m:real^3->bool)` THEN
    ASM_SIMP_TAC[INTERVAL_LENGTH_CUBE_POS]; ALL_TAC] THEN
  (* m != j *)
  SUBGOAL_THEN `~(m = j:real^3->bool)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(cj:real^3)$1 = interval_upperbound (v:real^3->bool) $ 1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Strict bounds: wpt in m's open interior *)
  SUBGOAL_THEN `interval_lowerbound (m:real^3->bool) $ 2 IN
       IMAGE (\k':real^3->bool. interval_lowerbound k' $ 2) D /\
     interval_upperbound (m:real^3->bool) $ 2 IN
       IMAGE (\k':real^3->bool. interval_upperbound k' $ 2) D /\
     interval_lowerbound (m:real^3->bool) $ 3 IN
       IMAGE (\k':real^3->bool. interval_lowerbound k' $ 3) D /\
     interval_upperbound (m:real^3->bool) $ 3 IN
       IMAGE (\k':real^3->bool. interval_upperbound k' $ 3) D`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `m:real^3->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(w2 = interval_lowerbound (m:real^3->bool) $ 2) /\
     ~(w2 = interval_upperbound (m:real^3->bool) $ 2) /\
     ~(w3 = interval_lowerbound (m:real^3->bool) $ 3) /\
     ~(w3 = interval_upperbound (m:real^3->bool) $ 3)`
    STRIP_ASSUME_TAC THENL [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    ASM_MESON_TAC[IN_IMAGE; IN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN `(cm:real^3)$2 < w2 /\ w2 < cm$2 + sm /\
     cm$3 < w3 /\ w3 < cm$3 + sm` STRIP_ASSUME_TAC THENL
   [(* Non-strict from membership, then avoidance makes strict *)
    SUBGOAL_THEN `(cm:real^3)$2 <= w2 /\ w2 <= cm$2 + sm /\
       cm$3 <= w3 /\ w3 <= cm$3 + sm` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(vector[interval_upperbound (v:real^3->bool) $ 1;
           w2; w3]:real^3) IN interval[cm:real^3, cm + sm % vec 1]`
        MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                  VEC_COMPONENT; REAL_MUL_RID; VECTOR_3] THEN
      REAL_ARITH_TAC; ALL_TAC] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y /\ ~(x = y) ==> x < y`) THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  (* Interior overlap: interior(m) ∩ interior(j) != {} *)
  SUBGOAL_THEN `~(interior (m:real^3->bool) INTER interior j = {})`
    MP_TAC THENL [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    ASM_REWRITE_TAC[INTERIOR_INTERVAL] THEN
    MESON_ASSUME_TAC [] `(cm:real^3)$1 = (ck:real^3)$1` THEN
    EXISTS_TAC `vector[(ck:real^3)$1 + sk + (min (sm - sk) sj) / &2;
              w2; w3]:real^3` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID; VECTOR_3] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN DISCH_TAC THEN
  UNDISCH_TAC `(D:(real^3->bool)->bool) division_of UNIONS D` THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2 o
    REWRITE_RULE[division_of]) THEN
  DISCH_THEN(MP_TAC o SPECL [`m:real^3->bool`; `j:real^3->bool`]) THEN
  ASM_REWRITE_TAC[];;

let VALLEY_DESCENT_CONTAINMENT = `!D (a:real^3) d (v:real^3->bool) k j.
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v /\
    k IN D /\
    interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
    (?z:real^3. z IN k /\
         interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\ z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
         interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\ z$3 < interval_upperbound (v:real^3->bool) $ 3) /\
    (!j'. j' IN D /\ ~(j' = k) /\
          interval_lowerbound j' $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
          (?z:real^3. z IN j' /\
               interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
               z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
               interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
               z$3 < interval_upperbound (v:real^3->bool) $ 3)
          ==> interval_length k < interval_length j') /\
    j IN D /\
    interval_lowerbound j $ 1 = interval_upperbound k $ 1 /\
    (?z:real^3. z IN j /\
         interval_lowerbound k $ 2 < z$2 /\ z$2 < interval_upperbound k $ 2 /\
         interval_lowerbound k $ 3 < z$3 /\ z$3 < interval_upperbound k $ 3)
    ==> interval_lowerbound k $ 2 <= interval_lowerbound j $ 2 /\
        interval_upperbound j $ 2 <= interval_upperbound k $ 2 /\
        interval_lowerbound k $ 3 <= interval_lowerbound j $ 3 /\
        interval_upperbound j $ 3 <= interval_upperbound k $ 3`;;

(* The smallest face cube has a neighbor: there must be another cube on v's face
   that is distinct from k and also overlaps v's interior in dims 2,3 *)

let VALLEY_FACE_EXISTS_ANOTHER = `!D (a:real^3) d (v:real^3->bool) (k:real^3->bool).
     &0 < d /\
     cube_dissection D /\
     UNIONS D = interval[a, a + d % vec 1] /\
     valley D v /\
     k IN D /\
     interval_lowerbound k $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
     (?z. z IN k /\
          interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
          z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
          interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
          z$3 < interval_upperbound (v:real^3->bool) $ 3) /\
     (!j'. j' IN D /\ ~(j' = k) /\
           interval_lowerbound j' $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
           (?z. z IN j' /\
                interval_lowerbound (v:real^3->bool) $ 2 < z$2 /\
                z$2 < interval_upperbound (v:real^3->bool) $ 2 /\
                interval_lowerbound (v:real^3->bool) $ 3 < z$3 /\
                z$3 < interval_upperbound (v:real^3->bool) $ 3)
           ==> interval_length k < interval_length j')
     ==> ?j0. j0 IN D /\ ~(j0 = k) /\
              interval_lowerbound j0 $ 1 = interval_upperbound (v:real^3->bool) $ 1 /\
              (?z'. z' IN j0 /\
                    interval_lowerbound (v:real^3->bool) $ 2 < z'$2 /\
                    z'$2 < interval_upperbound (v:real^3->bool) $ 2 /\
                    interval_lowerbound (v:real^3->bool) $ 3 < z'$3 /\
                    z'$3 < interval_upperbound (v:real^3->bool) $ 3)`;;

(* Key descent: any valley produces a smaller valley on an element of D *)

let VALLEY_DESCENT = `!D (a:real^3) d (v:real^3->bool).
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v
    ==> ?k. k IN D /\ interval_length k < interval_length v /\
            valley D k`;;

(* Impossibility: no cube dissection of an interval can have a valley *)

let VALLEY_IMPOSSIBLE = `!D (a:real^3) d (v:real^3->bool).
    &0 < d /\
    cube_dissection D /\
    UNIONS D = interval[a, a + d % vec 1] /\
    valley D v ==> F`;;

(* For the cube case: use VALLEY_INITIAL + VALLEY_IMPOSSIBLE *)
let ONLY_TRIVIAL_CUBE_DISSECTION_CUBE = `!(a:real^3) d D.
        &0 < d /\
        cube_dissection D /\
        UNIONS D = interval[a, a + d % vec 1]
        ==> D = {interval[a, a + d % vec 1]}`;;

(* Clean statement: a cube dissection of a cube is trivial *)

let ONLY_TRIVIAL_CUBE_DISSECTION = `!D:(real^3->bool)->bool.
        cube_dissection D /\ cube(UNIONS D) ==> D = {UNIONS D}`;;
