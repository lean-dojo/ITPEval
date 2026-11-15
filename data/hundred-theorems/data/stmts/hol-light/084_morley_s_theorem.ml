(* ========================================================================= *)
(* Formalization of Alain Connes's paper "A new proof of Morley's theorem".  *)
(* ========================================================================= *)

needs "Library/iter.ml";;
needs "Multivariate/geom.ml";;

(* ------------------------------------------------------------------------- *)
(* Reflection about the line[0,e^{i t}]                                      *)
(* ------------------------------------------------------------------------- *)

let reflect2d = new_definition
 `reflect2d t = rotate2d t o cnj o rotate2d(--t)`;;

let REFLECT2D_COMPOSE = `!s t. reflect2d s o reflect2d t = rotate2d (&2 * (s - t))`;;

(* ------------------------------------------------------------------------- *)
(* Rotation about point "a" by angle "t".                                    *)
(* ------------------------------------------------------------------------- *)

let rotate_about = new_definition
 `rotate_about a t x = a + rotate2d t (x - a)`;;

(* ------------------------------------------------------------------------- *)
(* Reflection across line (a,b).                                             *)
(* ------------------------------------------------------------------------- *)

let reflect_across = new_definition
 `reflect_across (a,b) x = a + reflect2d (Arg(b - a)) (x - a)`;;

let REFLECT_ACROSS_COMPOSE = `!a b c.
        ~(b = a) /\ ~(c = a)
        ==> reflect_across(a,b) o reflect_across(a,c) =
            rotate_about a (&2 * Arg((b - a) / (c - a)))`;;

let REFLECT_ACROSS_COMPOSE_ANGLE = `!a b c.
        ~(b = a) /\ ~(c = a) /\ &0 <= Im((c - a) / (b - a))
        ==> reflect_across(a,c) o reflect_across(a,b) =
            rotate_about a (&2 * angle(c,a,b))`;;

let REFLECT_ACROSS_COMPOSE_INVOLUTION = `!a b. ~(a = b) ==> reflect_across(a,b) o reflect_across(a,b) = I`;;

let REFLECT_ACROSS_SYM = `!a b. reflect_across(a,b) = reflect_across(b,a)`;;

(* ------------------------------------------------------------------------- *)
(* Some additional lemmas.                                                   *)
(* ------------------------------------------------------------------------- *)

let ITER_ROTATE_ABOUT = `!n a t. ITER n (rotate_about a t) = rotate_about a (&n * t)`;;

let REAL_LE_IM_DIV_CYCLIC = `!a b c. &0 <= Im ((c - a) / (b - a)) <=> &0 <= Im((a - b) / (c - b))`;;

let ROTATE_ABOUT_INVERT = `rotate_about a t w = z <=> w = rotate_about a (--t) z`;;

let ROTATE_EQ_REFLECT_LEMMA = `!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = t
        ==> rotate_about a t z = reflect_across (a,b) z`;;

let ROTATE_EQ_REFLECT_PI_LEMMA = `!a b z t.
        ~(b = a) /\ &2 * Arg((b - a) / (z - a)) = &4 * pi + t
        ==> rotate_about a t z = reflect_across (a,b) z`;;

(* ------------------------------------------------------------------------- *)
(* Algebraic characterization of equilateral triangle.                       *)
(* ------------------------------------------------------------------------- *)

let EQUILATERAL_TRIANGLE_ALGEBRAIC = `!A B C j.
        j pow 3 = Cx(&1) /\ ~(j = Cx(&1)) /\
        A + j * B + j pow 2 * C = Cx(&0)
        ==> dist(A,B) = dist(B,C) /\ dist(C,A) = dist(B,C)`;;

(* ------------------------------------------------------------------------- *)
(* The main algebraic lemma.                                                 *)
(* ------------------------------------------------------------------------- *)

let AFFINE_GROUP_ITER_3 = `ITER 3 (\z. a * z + b) = (\z. a pow 3 * z + b * (Cx(&1) + a + a pow 2))`;;

let AFFINE_GROUP_COMPOSE = `(\z. a1 * z + b1) o (\z. a2 * z + b2) =
   (\z. (a1 * a2) * z + (b1 + a1 * b2))`;;

let AFFINE_GROUP_I = `I = (\z. Cx(&1) * z + Cx(&0))`;;

let AFFINE_GROUP_EQ = `!a b a' b. (\z. a * z + b) = (\z. a' * z + b') <=> a = a' /\ b = b'`;;

let AFFINE_GROUP_ROTATE_ABOUT = `!a t. rotate_about a t =
         (\z. cexp(ii * Cx(t)) * z + (Cx(&1) - cexp(ii * Cx(t))) * a)`;;

let ALGEBRAIC_LEMMA = `!a1 a2 a3 b1 b2 b3 A B C.
        (\z. a3 * z + b3) ((\z. a1 * z + b1) B) = B /\
        (\z. a1 * z + b1) ((\z. a2 * z + b2) C) = C /\
        (\z. a2 * z + b2) ((\z. a3 * z + b3) A) = A /\
        ITER 3 (\z. a1 * z + b1) o ITER 3 (\z. a2 * z + b2) o
        ITER 3 (\z. a3 * z + b3) = I /\
        ~(a1 * a2 * a3 = Cx(&1)) /\
        ~(a1 * a2 = Cx(&1)) /\
        ~(a2 * a3 = Cx(&1)) /\
        ~(a3 * a1 = Cx(&1))
        ==> (a1 * a2 * a3) pow 3 = Cx (&1) /\
            ~(a1 * a2 * a3 = Cx (&1)) /\
            C + (a1 * a2 * a3) * A + (a1 * a2 * a3) pow 2 * B = Cx(&0)`;;

(* ------------------------------------------------------------------------- *)
(* A tactic to avoid some duplication over cyclic permutations.              *)
(* ------------------------------------------------------------------------- *)

let CYCLIC_PERM_SUBGOAL_THEN =
  let lemma = MESON[]
   `(!A B C P Q R a b c g1 g2 g3.
       Ant A B C P Q R a b c g1 g2 g3 ==> Cns A B C P Q R a b c g1 g2 g3)
    ==> (!A B C P Q R a b c g1 g2 g3.
           Ant A B C P Q R a b c g1 g2 g3
           ==> Ant B C A Q R P b c a g2 g3 g1)
        ==> (!A B C P Q R a b c g1 g2 g3.
                   Ant A B C P Q R a b c g1 g2 g3
                   ==> Cns A B C P Q R a b c g1 g2 g3 /\
                       Cns B C A Q R P b c a g2 g3 g1 /\
                       Cns C A B R P Q c a b g3 g1 g2)`
  and vars =
   [`A:complex`; `B:complex`; `C:complex`;
    `P:complex`; `Q:complex`; `R:complex`;
    `a:real`; `b:real`; `c:real`;
    `g1:complex->complex`; `g2:complex->complex`; `g3:complex->complex`] in
  fun t ttac (asl,w) ->
      let asm = list_mk_conj (map (concl o snd) (rev asl)) in
      let gnw = list_mk_forall(vars,mk_imp(asm,t)) in
      let th1 = MATCH_MP lemma (ASSUME gnw) in
      let tm1 = fst(dest_imp(concl th1)) in
      let th2 = REWRITE_CONV[INSERT_AC; CONJ_ACI; ANGLE_SYM; EQ_SYM_EQ] tm1 in
      let th3 = DISCH_ALL(MP th1 (EQT_ELIM th2)) in
      (MP_TAC th3 THEN ANTS_TAC THENL
        [POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT GEN_TAC THEN STRIP_TAC;
         DISCH_THEN(MP_TAC o SPEC_ALL) THEN ANTS_TAC THENL
          [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
           DISCH_THEN(CONJUNCTS_THEN2 ttac MP_TAC) THEN
           DISCH_THEN(CONJUNCTS_THEN ttac)]]) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Morley's theorem a la Connes.                                             *)
(* ------------------------------------------------------------------------- *)

let MORLEY = `!A B C:real^2 P Q R.
     ~collinear{A,B,C} /\ {P,Q,R} SUBSET convex hull {A,B,C} /\
     angle(A,B,R) = angle(A,B,C) / &3 /\
     angle(B,A,R) = angle(B,A,C) / &3 /\
     angle(B,C,P) = angle(B,C,A) / &3 /\
     angle(C,B,P) = angle(C,B,A) / &3 /\
     angle(C,A,Q) = angle(C,A,B) / &3 /\
     angle(A,C,Q) = angle(A,C,B) / &3
     ==> dist(R,P) = dist(P,Q) /\ dist(Q,R) = dist(P,Q)`;;
