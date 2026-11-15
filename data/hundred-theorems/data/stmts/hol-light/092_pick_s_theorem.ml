(* ========================================================================= *)
(* Pick's theorem.                                                           *)
(* ========================================================================= *)

needs "Multivariate/polytope.ml";;
needs "Multivariate/measure.ml";;
needs "Multivariate/moretop.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let COLLINEAR_IMP_NEGLIGIBLE = `!s:real^2->bool. collinear s ==> negligible s`;;

let CONVEX_HULL_3_0 = `!a b:real^N.
        convex hull {vec 0,a,b} =
        {x % a + y % b | &0 <= x /\ &0 <= y /\ x + y <= &1}`;;

let INTERIOR_CONVEX_HULL_3_0 = `!a b:real^2.
        ~(collinear {vec 0,a,b})
        ==> interior(convex hull {vec 0,a,b}) =
              {x % a + y % b | &0 < x /\ &0 < y /\ x + y < &1}`;;

let MEASURE_CONVEX_HULL_2_TRIVIAL = `(!a:real^2. measure(convex hull {a}) = &0) /\
   (!a b:real^2. measure(convex hull {a,b}) = &0)`;;

let NEGLIGIBLE_SEGMENT_2 = `!a b:real^2. negligible(segment[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Decomposing an additive function on a triangle.                           *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_DECOMPOSITION = `!a b c d:real^2.
        d IN convex hull {a,b,c}
        ==> (convex hull {a,b,c} =
             convex hull {d,b,c} UNION
             convex hull {d,a,c} UNION
             convex hull {d,a,b})`;;

let TRIANGLE_ADDITIVE_DECOMPOSITION = `!f:(real^2->bool)->real a b c d.
        (!s t. compact s /\ compact t
               ==> f(s UNION t) = f(s) + f(t) - f(s INTER t)) /\
        ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        ~affine_dependent {a,b,c} /\ d IN convex hull {a,b,c}
        ==> f(convex hull {a,b,c}) =
            (f(convex hull {a,b,d}) +
             f(convex hull {a,c,d}) +
             f(convex hull {b,c,d})) -
            (f(convex hull {a,d}) +
             f(convex hull {b,d}) +
             f(convex hull {c,d})) +
            f(convex hull {d})`;;

(* ------------------------------------------------------------------------- *)
(* Vectors all of whose coordinates are integers.                            *)
(* ------------------------------------------------------------------------- *)

let integral_vector = define
 `integral_vector(x:real^N) <=>
        !i. 1 <= i /\ i <= dimindex(:N) ==> integer(x$i)`;;

let INTEGRAL_VECTOR_VEC = `!n. integral_vector(vec n)`;;

let INTEGRAL_VECTOR_STDBASIS = `!i. integral_vector(basis i:real^N)`;;

let INTEGRAL_VECTOR_ADD = `!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x + y)`;;

let INTEGRAL_VECTOR_SUB = `!x y:real^N.
        integral_vector x /\ integral_vector y ==> integral_vector(x - y)`;;

let INTEGRAL_VECTOR_ADD_LCANCEL = `!x y:real^N.
        integral_vector x ==> (integral_vector(x + y) <=> integral_vector y)`;;

let FINITE_BOUNDED_INTEGER_POINTS = `!s:real^N->bool. bounded s ==> FINITE {x | x IN s /\ integral_vector x}`;;

let FINITE_TRIANGLE_INTEGER_POINTS = `!a b c:real^N. FINITE {x | x IN convex hull {a,b,c} /\ integral_vector x}`;;

(* ------------------------------------------------------------------------- *)
(* Properties of a basis for the integer lattice.                            *)
(* ------------------------------------------------------------------------- *)

let LINEAR_INTEGRAL_VECTOR = `!f:real^N->real^N.
        linear f
        ==> ((!x. integral_vector x ==> integral_vector(f x)) <=>
             (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N)
                    ==> integer(matrix f$i$j)))`;;

let INTEGRAL_BASIS_UNIMODULAR = `!f:real^N->real^N.
        linear f /\ IMAGE f integral_vector = integral_vector
        ==> abs(det(matrix f)) = &1`;;

(* ------------------------------------------------------------------------- *)
(* Pick's theorem for an elementary triangle.                                *)
(* ------------------------------------------------------------------------- *)

let PICK_ELEMENTARY_TRIANGLE_0 = `!a b:real^2.
        {x | x IN convex hull {vec 0,a,b} /\ integral_vector x} = {vec 0,a,b}
        ==> measure(convex hull {vec 0,a,b}) =
               if collinear {vec 0,a,b} then &0 else &1 / &2`;;

let PICK_ELEMENTARY_TRIANGLE = `!a b c:real^2.
        {x | x IN convex hull {a,b,c} /\ integral_vector x} = {a,b,c}
        ==> measure(convex hull {a,b,c}) =
               if collinear {a,b,c} then &0 else &1 / &2`;;

(* ------------------------------------------------------------------------- *)
(* Our form of Pick's theorem holds degenerately for a flat triangle.        *)
(* ------------------------------------------------------------------------- *)

let PICK_TRIANGLE_FLAT = `!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c /\
        c IN segment[a,b]
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`;;

(* ------------------------------------------------------------------------- *)
(* Pick's theorem for a triangle.                                            *)
(* ------------------------------------------------------------------------- *)

let PICK_TRIANGLE_ALT = `!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
             &(CARD {x | x IN convex hull {a,b,c} /\ integral_vector x}) -
             (&(CARD {x | x IN convex hull {b,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,c} /\ integral_vector x}) +
              &(CARD {x | x IN convex hull {a,b} /\ integral_vector x})) / &2 +
             &1 / &2`;;

let PICK_TRIANGLE = `!a b c:real^2.
        integral_vector a /\ integral_vector b /\ integral_vector c
        ==> measure(convex hull {a,b,c}) =
                if collinear {a,b,c} then &0
                else &(CARD {x | x IN interior(convex hull {a,b,c}) /\
                                 integral_vector x}) +
                     &(CARD {x | x IN frontier(convex hull {a,b,c}) /\
                                 integral_vector x}) / &2 - &1`;;

(* ------------------------------------------------------------------------- *)
(* Parity lemma for segment crossing a polygon.                              *)
(* ------------------------------------------------------------------------- *)

let PARITY_LEMMA = `!a b c d p x:real^2.
        simple_path(p ++ linepath(a,b)) /\
        pathstart p = b /\ pathfinish p = a /\
        segment(a,b) INTER segment(c,d) = {x} /\
        segment[c,d] INTER path_image p = {}
        ==> (c IN inside(path_image(p ++ linepath(a,b))) <=>
             d IN outside(path_image(p ++ linepath(a,b))))`;;

(* ------------------------------------------------------------------------- *)
(* Polygonal path; 0 in the empty case is just for linear invariance.        *)
(* Note that we *are* forced to assume non-emptiness for translation.        *)
(* ------------------------------------------------------------------------- *)

let polygonal_path = define
 `polygonal_path[] = linepath(vec 0,vec 0) /\
  polygonal_path[a] = linepath(a,a) /\
  polygonal_path [a;b] = linepath(a,b) /\
  polygonal_path (CONS a (CONS b (CONS c l))) =
       linepath(a,b) ++ polygonal_path(CONS b (CONS c l))`;;

let POLYGONAL_PATH_CONS_CONS = `!a b p. ~(p = [])
           ==> polygonal_path(CONS a (CONS b p)) =
               linepath(a,b) ++ polygonal_path(CONS b p)`;;

let POLYGONAL_PATH_TRANSLATION = `!a b p. polygonal_path (MAP (\x. a + x) (CONS b p)) =
         (\x. a + x) o (polygonal_path (CONS b p))`;;

add_translation_invariants [POLYGONAL_PATH_TRANSLATION];;

let POLYGONAL_PATH_LINEAR_IMAGE = `!f p. linear f ==> polygonal_path (MAP f p) = f o polygonal_path p`;;

add_linear_invariants [POLYGONAL_PATH_LINEAR_IMAGE];;

let PATHSTART_POLYGONAL_PATH = `!p. pathstart(polygonal_path p) = if p = [] then vec 0 else HD p`;;

let PATHFINISH_POLYGONAL_PATH = `!p. pathfinish(polygonal_path p) = if p = [] then vec 0 else LAST p`;;

let VERTICES_IN_PATH_IMAGE_POLYGONAL_PATH = `!p:(real^N)list. set_of_list p SUBSET path_image (polygonal_path p)`;;

let ARC_POLYGONAL_PATH_IMP_DISTINCT = `!p:(real^N)list. arc(polygonal_path p) ==> PAIRWISE (\x y. ~(x = y)) p`;;

let PATH_POLYGONAL_PATH = `!p:(real^N)list. path(polygonal_path p)`;;

let PATH_IMAGE_POLYGONAL_PATH_SUBSET_CONVEX_HULL = `!p. ~(p = [])
       ==> path_image(polygonal_path p) SUBSET convex hull (set_of_list p)`;;

let PATH_IMAGE_POLYGONAL_PATH_SUBSET_SEGMENTS = `!p x:real^N.
        arc(polygonal_path p) /\ 3 <= LENGTH p /\
        x IN path_image(polygonal_path p)
        ==> ?a b. MEM a p /\ MEM b p /\ x IN segment[a,b] /\
                  segment[a,b] SUBSET path_image(polygonal_path p) /\
                  ~(pathstart(polygonal_path p) IN segment[a,b] /\
                    pathfinish(polygonal_path p) IN segment[a,b])`;;

(* ------------------------------------------------------------------------- *)
(* Rotating the starting point to move a preferred vertex forward.           *)
(* ------------------------------------------------------------------------- *)

let SET_OF_LIST_POLYGONAL_PATH_ROTATE = `!p. ~(p = []) ==> set_of_list(CONS (LAST p) (BUTLAST p)) = set_of_list p`;;

let PROPERTIES_POLYGONAL_PATH_SNOC = `!p d:real^N.
        2 <= LENGTH p
        ==> path_image(polygonal_path(APPEND p [d])) =
            path_image(polygonal_path p ++ linepath(LAST p,d)) /\
            (arc(polygonal_path(APPEND p [d])) <=>
             arc(polygonal_path p ++ linepath(LAST p,d))) /\
            (simple_path(polygonal_path(APPEND p [d])) <=>
             simple_path(polygonal_path p ++ linepath(LAST p,d)))`;;

let PATH_IMAGE_POLYGONAL_PATH_ROTATE = `!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> path_image(polygonal_path(APPEND (TL p) [HD(TL p)])) =
            path_image(polygonal_path p)`;;

let SIMPLE_PATH_POLYGONAL_PATH_ROTATE = `!p:(real^N)list.
        2 <= LENGTH p /\ LAST p = HD p
        ==> (simple_path(polygonal_path(APPEND (TL p) [HD(TL p)])) =
             simple_path(polygonal_path p))`;;

let ROTATE_LIST_TO_FRONT_1 = `!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. EL 1 l' = a /\ P l'`;;

let ROTATE_LIST_TO_FRONT_0 = `!P l a:A.
      (!l. P(l) ==> 3 <= LENGTH l /\ LAST l = HD l) /\
      (!l. P(l) ==> P(APPEND (TL l) [HD(TL l)])) /\
      P l /\ MEM a l
      ==> ?l'. HD l' = a /\ P l'`;;

(* ------------------------------------------------------------------------- *)
(* We can pick a transformation to make all y coordinates distinct.          *)
(* ------------------------------------------------------------------------- *)

let DISTINGUISHING_ROTATION_EXISTS_PAIR = `!x y. ~(x = y)
         ==> FINITE {t | &0 <= t /\ t < &2 * pi /\
                         (rotate2d t x)$2 = (rotate2d t y)$2}`;;

let DISTINGUISHING_ROTATION_EXISTS = `!s. FINITE s ==> ?t. pairwise (\x y. ~(x$2 = y$2)) (IMAGE (rotate2d t) s)`;;

let DISTINGUISHING_ROTATION_EXISTS_POLYGON = `!p:(real^2)list.
        ?f q. (?g. orthogonal_transformation g /\ f = MAP g) /\
              (!x y. MEM x q /\ MEM y q /\ ~(x = y) ==> ~(x$2 = y$2)) /\
              f q = p`;;

(* ------------------------------------------------------------------------- *)
(* Proof that we can chop a polygon's inside in two.                         *)
(* ------------------------------------------------------------------------- *)

let POLYGON_CHOP_IN_TWO = `!p:(real^2)list.
        simple_path(polygonal_path p) /\
        pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
        5 <= LENGTH p
        ==> ?a b. ~(a = b) /\ MEM a p /\ MEM b p /\
                  segment(a,b) SUBSET inside(path_image(polygonal_path p))`;;

(* ------------------------------------------------------------------------- *)
(* Hence the final Pick theorem by induction on number of polygon segments.  *)
(* ------------------------------------------------------------------------- *)

let PICK = `!p:(real^2)list.
        (!x. MEM x p ==> integral_vector x) /\
        simple_path (polygonal_path p) /\
        pathfinish (polygonal_path p) = pathstart (polygonal_path p)
        ==> measure(inside(path_image(polygonal_path p))) =
                &(CARD {x | x IN inside(path_image(polygonal_path p)) /\
                            integral_vector x}) +
                &(CARD {x | x IN path_image(polygonal_path p) /\
                            integral_vector x}) / &2 - &1`;;
