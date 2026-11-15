(* ========================================================================= *)
(* Pascal's hexagon theorem for projective and affine planes.                *)
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
(* Conics and bracket condition for 6 points to be on a conic.               *)
(* ------------------------------------------------------------------------- *)

let homogeneous_conic = new_definition
 `homogeneous_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^3 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$3 pow 2 +
                         d * x$1 * x$2 + e * x$1 * x$3 + f * x$2 * x$3 = &0}`;;

let projective_conic = new_definition
 `projective_conic con <=>
        ?c. homogeneous_conic c /\ con = {p | (homop p) IN c}`;;

let HOMOGENEOUS_CONIC_BRACKET = `!con x1 x2 x3 x4 x5 x6.
        homogeneous_conic con /\
        x1 IN con /\ x2 IN con /\ x3 IN con /\
        x4 IN con /\ x5 IN con /\ x6 IN con
        ==> det(vector[x6;x1;x4]) * det(vector[x6;x2;x3]) *
            det(vector[x5;x1;x3]) * det(vector[x5;x2;x4]) =
            det(vector[x6;x1;x3]) * det(vector[x6;x2;x4]) *
            det(vector[x5;x1;x4]) * det(vector[x5;x2;x3])`;;

let PROJECTIVE_CONIC_BRACKET = `!con p1 p2 p3 p4 p5 p6.
        projective_conic con /\
        p1 IN con /\ p2 IN con /\ p3 IN con /\
        p4 IN con /\ p5 IN con /\ p6 IN con
        ==> bracket[p6;p1;p4] * bracket[p6;p2;p3] *
            bracket[p5;p1;p3] * bracket[p5;p2;p4] =
            bracket[p6;p1;p3] * bracket[p6;p2;p4] *
            bracket[p5;p1;p4] * bracket[p5;p2;p3]`;;

(* ------------------------------------------------------------------------- *)
(* Pascal's theorem with all the nondegeneracy principles we use directly.   *)
(* ------------------------------------------------------------------------- *)

let PASCAL_DIRECT = `!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x2,x5,x7} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x4,x6} /\
        ~COLLINEAR {x3,x4,x5} /\
        ~COLLINEAR {x1,x5,x7} /\
        ~COLLINEAR {x2,x5,x9} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x3,x6,x8} /\
        ~COLLINEAR {x2,x4,x5} /\
        ~COLLINEAR {x2,x4,x7} /\
        ~COLLINEAR {x2,x6,x8} /\
        ~COLLINEAR {x3,x4,x6} /\
        ~COLLINEAR {x3,x5,x8} /\
        ~COLLINEAR {x1,x3,x5}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}`;;

(* ------------------------------------------------------------------------- *)
(* With longer but more intuitive non-degeneracy conditions, basically that  *)
(* the 6 points divide into two groups of 3 and no 3 are collinear unless    *)
(* they are all in the same group.                                           *)
(* ------------------------------------------------------------------------- *)

let PASCAL = `!con x1 x2 x3 x4 x5 x6 x6 x8 x9.
        ~COLLINEAR {x1,x2,x4} /\
        ~COLLINEAR {x1,x2,x5} /\
        ~COLLINEAR {x1,x2,x6} /\
        ~COLLINEAR {x1,x3,x4} /\
        ~COLLINEAR {x1,x3,x5} /\
        ~COLLINEAR {x1,x3,x6} /\
        ~COLLINEAR {x2,x3,x4} /\
        ~COLLINEAR {x2,x3,x5} /\
        ~COLLINEAR {x2,x3,x6} /\
        ~COLLINEAR {x4,x5,x1} /\
        ~COLLINEAR {x4,x5,x2} /\
        ~COLLINEAR {x4,x5,x3} /\
        ~COLLINEAR {x4,x6,x1} /\
        ~COLLINEAR {x4,x6,x2} /\
        ~COLLINEAR {x4,x6,x3} /\
        ~COLLINEAR {x5,x6,x1} /\
        ~COLLINEAR {x5,x6,x2} /\
        ~COLLINEAR {x5,x6,x3}
        ==> projective_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            COLLINEAR {x1,x9,x5} /\
            COLLINEAR {x1,x8,x6} /\
            COLLINEAR {x2,x9,x4} /\
            COLLINEAR {x2,x7,x6} /\
            COLLINEAR {x3,x8,x4} /\
            COLLINEAR {x3,x7,x5}
            ==> COLLINEAR {x7,x8,x9}`;;

(* ------------------------------------------------------------------------- *)
(* Homogenization and hence mapping from affine to projective plane.         *)
(* ------------------------------------------------------------------------- *)

let homogenize = new_definition
 `(homogenize:real^2->real^3) x = vector[x$1; x$2; &1]`;;

let projectivize = new_definition
 `projectivize = projp o homogenize`;;

let HOMOGENIZE_NONZERO = `!x. ~(homogenize x = vec 0)`;;

(* ------------------------------------------------------------------------- *)
(* Conic in affine plane.                                                    *)
(* ------------------------------------------------------------------------- *)

let affine_conic = new_definition
 `affine_conic con <=>
    ?a b c d e f.
       ~(a = &0 /\ b = &0 /\ c = &0 /\ d = &0 /\ e = &0 /\ f = &0) /\
       con = {x:real^2 | a * x$1 pow 2 + b * x$2 pow 2 + c * x$1 * x$2 +
                         d * x$1 + e * x$2 + f = &0}`;;

(* ------------------------------------------------------------------------- *)
(* Relationships between affine and projective notions.                      *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_PROJECTIVIZE = `!a b c. collinear{a,b,c} <=>
           COLLINEAR{projectivize a,projectivize b,projectivize c}`;;

let AFFINE_PROJECTIVE_CONIC = `!con. affine_conic con <=> ?con'. projective_conic con' /\
                                     con = {x | projectivize x IN con'}`;;

(* ------------------------------------------------------------------------- *)
(* Hence Pascal's theorem for the affine plane.                              *)
(* ------------------------------------------------------------------------- *)

let PASCAL_AFFINE = `!con x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        ~collinear {x1,x2,x4} /\
        ~collinear {x1,x2,x5} /\
        ~collinear {x1,x2,x6} /\
        ~collinear {x1,x3,x4} /\
        ~collinear {x1,x3,x5} /\
        ~collinear {x1,x3,x6} /\
        ~collinear {x2,x3,x4} /\
        ~collinear {x2,x3,x5} /\
        ~collinear {x2,x3,x6} /\
        ~collinear {x4,x5,x1} /\
        ~collinear {x4,x5,x2} /\
        ~collinear {x4,x5,x3} /\
        ~collinear {x4,x6,x1} /\
        ~collinear {x4,x6,x2} /\
        ~collinear {x4,x6,x3} /\
        ~collinear {x5,x6,x1} /\
        ~collinear {x5,x6,x2} /\
        ~collinear {x5,x6,x3}
        ==> affine_conic con /\
            x1 IN con /\ x2 IN con /\ x3 IN con /\
            x4 IN con /\ x5 IN con /\ x6 IN con /\
            collinear {x1,x9,x5} /\
            collinear {x1,x8,x6} /\
            collinear {x2,x9,x4} /\
            collinear {x2,x7,x6} /\
            collinear {x3,x8,x4} /\
            collinear {x3,x7,x5}
            ==> collinear {x7,x8,x9}`;;

(* ------------------------------------------------------------------------- *)
(* Special case of a circle where nondegeneracy is simpler.                  *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_NOT_COCIRCULAR = `!r c x y z:real^2.
        dist(c,x) = r /\ dist(c,y) = r /\ dist(c,z) = r /\
        ~(x = y) /\ ~(x = z) /\ ~(y = z)
        ==> ~collinear {x,y,z}`;;

let PASCAL_AFFINE_CIRCLE = `!c r x1 x2 x3 x4 x5 x6 x7 x8 x9:real^2.
        PAIRWISE (\x y. ~(x = y)) [x1;x2;x3;x4;x5;x6] /\
        dist(c,x1) = r /\ dist(c,x2) = r /\ dist(c,x3) = r /\
        dist(c,x4) = r /\ dist(c,x5) = r /\ dist(c,x6) = r /\
        collinear {x1,x9,x5} /\
        collinear {x1,x8,x6} /\
        collinear {x2,x9,x4} /\
        collinear {x2,x7,x6} /\
        collinear {x3,x8,x4} /\
        collinear {x3,x7,x5}
        ==> collinear {x7,x8,x9}`;;
