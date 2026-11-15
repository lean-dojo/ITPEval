(* ========================================================================= *)
(* #87: Desargues's theorem.                                                 *)
(* ========================================================================= *)

needs "Multivariate/cross.ml";;

(* ------------------------------------------------------------------------- *)
(* A lemma we want to justify some of the axioms.                            *)
(* ------------------------------------------------------------------------- *)

let NORMAL_EXISTS = `!u v:real^3. ?w. ~(w = vec 0) /\ orthogonal u w /\ orthogonal v w`;;

(* ------------------------------------------------------------------------- *)
(* Type of directions.                                                       *)
(* ------------------------------------------------------------------------- *)

let direction_tybij = new_type_definition "direction" ("mk_dir","dest_dir")
 (MESON[BASIS_NONZERO; LE_REFL; DIMINDEX_GE_1] `?x:real^3. ~(x = vec 0)`);;

parse_as_infix("||",(11,"right"));;
parse_as_infix("_|_",(11,"right"));;

let perpdir = new_definition
 `x _|_ y <=> orthogonal (dest_dir x) (dest_dir y)`;;

let pardir = new_definition
 `x || y <=> (dest_dir x) cross (dest_dir y) = vec 0`;;

let DIRECTION_CLAUSES = `((!x. P(dest_dir x)) <=> (!x. ~(x = vec 0) ==> P x)) /\
   ((?x. P(dest_dir x)) <=> (?x. ~(x = vec 0) /\ P x))`;;

let [PARDIR_REFL; PARDIR_SYM; PARDIR_TRANS] = (CONJUNCTS o prove)
 (`(!x. x || x) /\
   (!x y. x || y <=> y || x) /\
   (!x y z. x || y /\ y || z ==> x || z)`,
  REWRITE_TAC[pardir; DIRECTION_CLAUSES] THEN VEC3_TAC);;

let PARDIR_EQUIV = `!x y. ((||) x = (||) y) <=> x || y`;;

let DIRECTION_AXIOM_1 = `!p p'. ~(p || p') ==> ?l. p _|_ l /\ p' _|_ l /\
                             !l'. p _|_ l' /\ p' _|_ l' ==> l' || l`;;

let DIRECTION_AXIOM_2 = `!l l'. ?p. p _|_ l /\ p _|_ l'`;;

let DIRECTION_AXIOM_3 = `?p p' p''.
        ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
        ~(?l. p _|_ l /\ p' _|_ l /\ p'' _|_ l)`;;

let DIRECTION_AXIOM_4_WEAK = `!l. ?p p'. ~(p || p') /\ p _|_ l /\ p' _|_ l`;;

let ORTHOGONAL_COMBINE = `!x a b. a _|_ x /\ b _|_ x /\ ~(a || b)
           ==> ?c. c _|_ x /\ ~(a || c) /\ ~(b || c)`;;

let DIRECTION_AXIOM_4 = `!l. ?p p' p''. ~(p || p') /\ ~(p' || p'') /\ ~(p || p'') /\
                  p _|_ l /\ p' _|_ l /\ p'' _|_ l`;;

let line_tybij = define_quotient_type "line" ("mk_line","dest_line") `(||)`;;

let PERPDIR_WELLDEF = `!x y x' y'. x || x' /\ y || y' ==> (x _|_ y <=> x' _|_ y')`;;

let perpl,perpl_th =
  lift_function (snd line_tybij) (PARDIR_REFL,PARDIR_TRANS)
                "perpl" PERPDIR_WELLDEF;;

let line_lift_thm = lift_theorem line_tybij
 (PARDIR_REFL,PARDIR_SYM,PARDIR_TRANS) [perpl_th];;

let LINE_AXIOM_1 = line_lift_thm DIRECTION_AXIOM_1;;
let LINE_AXIOM_2 = line_lift_thm DIRECTION_AXIOM_2;;
let LINE_AXIOM_3 = line_lift_thm DIRECTION_AXIOM_3;;
let LINE_AXIOM_4 = line_lift_thm DIRECTION_AXIOM_4;;

let point_tybij = new_type_definition "point" ("mk_point","dest_point")
 (prove(`?x:line. T`,REWRITE_TAC[]));;

parse_as_infix("on",(11,"right"));;

let on = new_definition `p on l <=> perpl (dest_point p) l`;;

let POINT_CLAUSES = `((p = p') <=> (dest_point p = dest_point p')) /\
   ((!p. P (dest_point p)) <=> (!l. P l)) /\
   ((?p. P (dest_point p)) <=> (?l. P l))`;;

let POINT_TAC th = REWRITE_TAC[on; POINT_CLAUSES] THEN ACCEPT_TAC th;;

let AXIOM_1 = `!p p'. ~(p = p') ==> ?l. p on l /\ p' on l /\
          !l'. p on l' /\ p' on l' ==> (l' = l)`;;

let AXIOM_2 = `!l l'. ?p. p on l /\ p on l'`;;

let AXIOM_3 = `?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    ~(?l. p on l /\ p' on l /\ p'' on l)`;;

let AXIOM_4 = `!l. ?p p' p''. ~(p = p') /\ ~(p' = p'') /\ ~(p = p'') /\
    p on l /\ p' on l /\ p'' on l`;;

(* ------------------------------------------------------------------------- *)
(* Mappings from vectors in R^3 to projective lines and points.              *)
(* ------------------------------------------------------------------------- *)

let projl = new_definition
 `projl x = mk_line((||) (mk_dir x))`;;

let projp = new_definition
 `projp x = mk_point(projl x)`;;

(* ------------------------------------------------------------------------- *)
(* Mappings in the other direction, to (some) homogeneous coordinates.       *)
(* ------------------------------------------------------------------------- *)

let PROJL_TOTAL = `!l. ?x. ~(x = vec 0) /\ l = projl x`;;

let homol = new_specification ["homol"]
  (REWRITE_RULE[SKOLEM_THM] PROJL_TOTAL);;

let PROJP_TOTAL = `!p. ?x. ~(x = vec 0) /\ p = projp x`;;

let homop_def = new_definition
 `homop p = homol(dest_point p)`;;

let homop = `!p. ~(homop p = vec 0) /\ p = projp(homop p)`;;

(* ------------------------------------------------------------------------- *)
(* Key equivalences of concepts in projective space and homogeneous coords.  *)
(* ------------------------------------------------------------------------- *)

let parallel = new_definition
 `parallel x y <=> x cross y = vec 0`;;

let ON_HOMOL = `!p l. p on l <=> orthogonal (homop p) (homol l)`;;

let EQ_HOMOL = `!l l'. l = l' <=> parallel (homol l) (homol l')`;;

let EQ_HOMOP = `!p p'. p = p' <=> parallel (homop p) (homop p')`;;

(* ------------------------------------------------------------------------- *)
(* A "welldefinedness" result for homogeneous coordinate map.                *)
(* ------------------------------------------------------------------------- *)

let PARALLEL_PROJL_HOMOL = `!x. parallel x (homol(projl x))`;;

let PARALLEL_PROJP_HOMOP = `!x. parallel x (homop(projp x))`;;

let PARALLEL_PROJP_HOMOP_EXPLICIT = `!x. ~(x = vec 0) ==> ?a. ~(a = &0) /\ homop(projp x) = a % x`;;

(* ------------------------------------------------------------------------- *)
(* Brackets, collinearity and their connection.                              *)
(* ------------------------------------------------------------------------- *)

let bracket = define
 `bracket[a;b;c] = det(vector[homop a;homop b;homop c])`;;

let COLLINEAR = new_definition
 `COLLINEAR s <=> ?l. !p. p IN s ==> p on l`;;

let COLLINEAR_SINGLETON = `!a. COLLINEAR {a}`;;

let COLLINEAR_PAIR = `!a b. COLLINEAR{a,b}`;;

let COLLINEAR_TRIPLE = `!a b c. COLLINEAR{a,b,c} <=> ?l. a on l /\ b on l /\ c on l`;;

let COLLINEAR_BRACKET = `!p1 p2 p3. COLLINEAR {p1,p2,p3} <=> bracket[p1;p2;p3] = &0`;;

(* ------------------------------------------------------------------------- *)
(* Rather crude shuffling of bracket triple into canonical order.            *)
(* ------------------------------------------------------------------------- *)

let BRACKET_SWAP,BRACKET_SHUFFLE = (CONJ_PAIR o prove)
 (`bracket[x;y;z] = --bracket[x;z;y] /\
   bracket[x;y;z] = bracket[y;z;x] /\
   bracket[x;y;z] = bracket[z;x;y]`,
  REWRITE_TAC[bracket; DET_3; VECTOR_3] THEN CONV_TAC REAL_RING);;

let BRACKET_SWAP_CONV =
  let conv = GEN_REWRITE_CONV I [BRACKET_SWAP] in
  fun tm -> let th = conv tm in
            let tm' = rand(rand(concl th)) in
            if term_order tm tm' then th else failwith "BRACKET_SWAP_CONV";;

(* ------------------------------------------------------------------------- *)
(* Direct proof following Richter-Gebert's "Meditations on Ceva's Theorem",  *)
(* except for a change of variable names. The degenerate conditions here are *)
(* just those that naturally get used in the proof.                          *)
(* ------------------------------------------------------------------------- *)

let DESARGUES_DIRECT = `~COLLINEAR {A',B,S} /\
   ~COLLINEAR {A,P,C} /\
   ~COLLINEAR {A,P,R} /\
   ~COLLINEAR {A,C,B} /\
   ~COLLINEAR {A,B,R} /\
   ~COLLINEAR {C',P,A'} /\
   ~COLLINEAR {C',P,B} /\
   ~COLLINEAR {C',P,B'} /\
   ~COLLINEAR {C',A',S} /\
   ~COLLINEAR {C',A',B'} /\
   ~COLLINEAR {P,C,A'} /\
   ~COLLINEAR {P,C,B} /\
   ~COLLINEAR {P,A',R} /\
   ~COLLINEAR {P,B,Q} /\
   ~COLLINEAR {P,Q,B'} /\
   ~COLLINEAR {C,B,S} /\
   ~COLLINEAR {A',Q,B'}
   ==> COLLINEAR {P,A',A} /\
       COLLINEAR {P,B,B'} /\
       COLLINEAR {P,C',C} /\
       COLLINEAR {B,C,Q} /\
       COLLINEAR {B',C',Q} /\
       COLLINEAR {A,R,C} /\
       COLLINEAR {A',C',R} /\
       COLLINEAR {B,S,A} /\
       COLLINEAR {A',S,B'}
       ==> COLLINEAR {Q,S,R}`;;
