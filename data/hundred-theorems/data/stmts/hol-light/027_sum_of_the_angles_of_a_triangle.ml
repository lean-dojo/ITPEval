(* ========================================================================= *)
(* Some geometric notions in real^N.                                         *)
(* ========================================================================= *)

needs "Multivariate/realanalysis.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* Pythagoras's theorem is almost immediate.                                 *)
(* ------------------------------------------------------------------------- *)

let PYTHAGORAS = `!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> norm(C - A) pow 2 = norm(B - A) pow 2 + norm(C - B) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* Angle between vectors (always 0 <= angle <= pi).                          *)
(* ------------------------------------------------------------------------- *)

let vector_angle = new_definition
 `vector_angle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`;;

let VECTOR_ANGLE_LINEAR_IMAGE_EQ = `!f x y. linear f /\ (!x. norm(f x) = norm x)
           ==> (vector_angle (f x) (f y) = vector_angle x y)`;;

add_linear_invariants [VECTOR_ANGLE_LINEAR_IMAGE_EQ];;

let VECTOR_ANGLE_ORTHOGONAL_TRANSFORMATION = `!f x y:real^N.
        orthogonal_transformation f
        ==> vector_angle (f x) (f y) = vector_angle x y`;;

(* ------------------------------------------------------------------------- *)
(* Basic properties of vector angles.                                        *)
(* ------------------------------------------------------------------------- *)

let VECTOR_ANGLE_REFL = `!x. vector_angle x x = if x = vec 0 then pi / &2 else &0`;;

let VECTOR_ANGLE_SYM = `!x y. vector_angle x y = vector_angle y x`;;

let VECTOR_ANGLE_LMUL = `!a x y:real^N.
        vector_angle (a % x) y =
                if a = &0 then pi / &2
                else if &0 <= a then vector_angle x y
                else pi - vector_angle x y`;;

let VECTOR_ANGLE_RMUL = `!a x y:real^N.
        vector_angle x (a % y) =
                if a = &0 then pi / &2
                else if &0 <= a then vector_angle x y
                else pi - vector_angle x y`;;

let VECTOR_ANGLE_LNEG = `!x y. vector_angle (--x) y = pi - vector_angle x y`;;

let VECTOR_ANGLE_RNEG = `!x y. vector_angle x (--y) = pi - vector_angle x y`;;

let VECTOR_ANGLE_NEG2 = `!x y. vector_angle (--x) (--y) = vector_angle x y`;;

let SIN_VECTOR_ANGLE_LMUL = `!a x y:real^N.
        sin(vector_angle (a % x) y) =
        if a = &0 then &1 else sin(vector_angle x y)`;;

let SIN_VECTOR_ANGLE_RMUL = `!a x y:real^N.
        sin(vector_angle x (a % y)) =
        if a = &0 then &1 else sin(vector_angle x y)`;;

let VECTOR_ANGLE = `!x y:real^N. x dot y = norm(x) * norm(y) * cos(vector_angle x y)`;;

let VECTOR_ANGLE_RANGE = `!x y:real^N. &0 <= vector_angle x y /\ vector_angle x y <= pi`;;

let ORTHOGONAL_VECTOR_ANGLE = `!x y:real^N. orthogonal x y <=> vector_angle x y = pi / &2`;;

let VECTOR_ANGLE_EQ_0 = `!x y:real^N. vector_angle x y = &0 <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\ norm(x) % y = norm(y) % x`;;

let VECTOR_ANGLE_EQ_PI = `!x y:real^N. vector_angle x y = pi <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\
                norm(x) % y + norm(y) % x = vec 0`;;

let VECTOR_ANGLE_EQ_0_DIST = `!x y:real^N. vector_angle x y = &0 <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\ norm(x + y) = norm x + norm y`;;

let VECTOR_ANGLE_EQ_PI_DIST = `!x y:real^N. vector_angle x y = pi <=>
                ~(x = vec 0) /\ ~(y = vec 0) /\ norm(x - y) = norm x + norm y`;;

let SIN_VECTOR_ANGLE_POS = `!v w. &0 <= sin(vector_angle v w)`;;

let SIN_VECTOR_ANGLE_EQ_0 = `!x y. sin(vector_angle x y) = &0 <=>
           vector_angle x y = &0 \/ vector_angle x y = pi`;;

let ASN_SIN_VECTOR_ANGLE = `!x y:real^N.
        asn(sin(vector_angle x y)) =
          if vector_angle x y <= pi / &2 then vector_angle x y
          else pi - vector_angle x y`;;

let SIN_VECTOR_ANGLE_EQ = `!x y w z.
        sin(vector_angle x y) = sin(vector_angle w z) <=>
            vector_angle x y = vector_angle w z \/
            vector_angle x y = pi - vector_angle w z`;;

let CONTINUOUS_WITHIN_CX_VECTOR_ANGLE_COMPOSE = `!f:real^M->real^N g x s.
     ~(f x = vec 0) /\ ~(g x = vec 0) /\
     f continuous (at x within s) /\
     g continuous (at x within s)
     ==> (\x. Cx(vector_angle (f x) (g x))) continuous (at x within s)`;;

let CONTINUOUS_AT_CX_VECTOR_ANGLE = `!c x:real^N. ~(x = vec 0) ==> (Cx o vector_angle c) continuous (at x)`;;

let CONTINUOUS_WITHIN_CX_VECTOR_ANGLE = `!c x:real^N s.
     ~(x = vec 0) ==> (Cx o vector_angle c) continuous (at x within s)`;;

let REAL_CONTINUOUS_AT_VECTOR_ANGLE = `!c x:real^N. ~(x = vec 0) ==> (vector_angle c) real_continuous (at x)`;;

let REAL_CONTINUOUS_WITHIN_VECTOR_ANGLE = `!c s x:real^N. ~(x = vec 0)
                  ==> (vector_angle c) real_continuous (at x within s)`;;

let CONTINUOUS_ON_CX_VECTOR_ANGLE = `!s. ~(vec 0 IN s) ==> (Cx o vector_angle c) continuous_on s`;;

let VECTOR_ANGLE_EQ = `!u v x y. ~(u = vec 0) /\  ~(v = vec 0) /\ ~(x = vec 0) /\ ~(y = vec 0)
             ==> (vector_angle u v = vector_angle x y <=>
                        (x dot y) * norm(u) * norm(v) =
                        (u dot v) * norm(x) * norm(y))`;;

let COS_VECTOR_ANGLE_EQ = `!u v x y.
        cos(vector_angle u v) = cos(vector_angle x y) <=>
        vector_angle u v = vector_angle x y`;;

let COLLINEAR_VECTOR_ANGLE = `!x y. ~(x = vec 0) /\ ~(y = vec 0)
         ==> (collinear {vec 0,x,y} <=>
                vector_angle x y = &0 \/ vector_angle x y = pi)`;;

let COLLINEAR_SIN_VECTOR_ANGLE = `!x y. ~(x = vec 0) /\ ~(y = vec 0)
         ==> (collinear {vec 0,x,y} <=> sin(vector_angle x y) = &0)`;;

let COLLINEAR_SIN_VECTOR_ANGLE_IMP = `!x y. sin(vector_angle x y) = &0
         ==> ~(x = vec 0) /\ ~(y = vec 0) /\ collinear {vec 0,x,y}`;;

let VECTOR_ANGLE_EQ_0_RIGHT = `!x y z:real^N. vector_angle x y = &0
                  ==> (vector_angle x z = vector_angle y z)`;;

let VECTOR_ANGLE_EQ_0_LEFT = `!x y z:real^N. vector_angle x y = &0
                  ==> (vector_angle z x = vector_angle z y)`;;

let VECTOR_ANGLE_EQ_PI_RIGHT = `!x y z:real^N. vector_angle x y = pi
                  ==> (vector_angle x z = pi - vector_angle y z)`;;

let VECTOR_ANGLE_EQ_PI_LEFT = `!x y z:real^N. vector_angle x y = pi
                  ==> (vector_angle z x = pi - vector_angle z y)`;;

let COS_VECTOR_ANGLE = `!x y:real^N.
        cos(vector_angle x y) = if x = vec 0 \/ y = vec 0 then &0
                                else (x dot y) / (norm x * norm y)`;;

let SIN_VECTOR_ANGLE = `!x y:real^N.
        sin(vector_angle x y) =
            if x = vec 0 \/ y = vec 0 then &1
            else sqrt(&1 - ((x dot y) / (norm x * norm y)) pow 2)`;;

let SIN_SQUARED_VECTOR_ANGLE = `!x y:real^N.
        sin(vector_angle x y) pow 2 =
            if x = vec 0 \/ y = vec 0 then &1
            else &1 - ((x dot y) / (norm x * norm y)) pow 2`;;

let VECTOR_ANGLE_COMPLEX_LMUL = `!a. ~(a = Cx(&0))
       ==> vector_angle (a * x) (a * y) = vector_angle x y`;;

let VECTOR_ANGLE_1 = `!x. vector_angle x (Cx(&1)) = acs(Re x / norm x)`;;

let ARG_EQ_VECTOR_ANGLE_1 = `!z. ~(z = Cx(&0)) /\ &0 <= Im z ==> Arg z = vector_angle z (Cx(&1))`;;

let VECTOR_ANGLE_ARG = `!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
         ==> vector_angle w z = if &0 <= Im(z / w) then Arg(z / w)
                                else &2 * pi - Arg(z / w)`;;

let VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY = `!f:real^N->real^N.
      linear f /\ (!x y. vector_angle (f x) (f y) = vector_angle x y) <=>
      ?c g. ~(c = &0) /\ orthogonal_transformation g /\ f = \z. c % g z`;;

let VECTOR_ANGLE_PRESERVING_EQ_SIMILARITY_ALT = `!f:real^N->real^N.
      linear f /\ (!x y. vector_angle (f x) (f y) = vector_angle x y) <=>
      ?c g. &0 < c /\ orthogonal_transformation g /\ f = \z. c % g z`;;

(* ------------------------------------------------------------------------- *)
(* Traditional geometric notion of angle (always 0 <= theta <= pi).          *)
(* ------------------------------------------------------------------------- *)

let angle = new_definition
 `angle(a,b,c) = vector_angle (a - b) (c - b)`;;

let ANGLE_LINEAR_IMAGE_EQ = `!f a b c.
        linear f /\ (!x. norm(f x) = norm x)
        ==> angle(f a,f b,f c) = angle(a,b,c)`;;

add_linear_invariants [ANGLE_LINEAR_IMAGE_EQ];;

let ANGLE_TRANSLATION_EQ = `!a b c d. angle(a + b,a + c,a + d) = angle(b,c,d)`;;

add_translation_invariants [ANGLE_TRANSLATION_EQ];;

let VECTOR_ANGLE_ANGLE = `vector_angle x y = angle(x,vec 0,y)`;;

let ANGLE_EQ_PI_DIST = `!A B C:real^N.
        angle(A,B,C) = pi <=>
        ~(A = B) /\ ~(C = B) /\ dist(A,C) = dist(A,B) + dist(B,C)`;;

let SIN_ANGLE_POS = `!A B C. &0 <= sin(angle(A,B,C))`;;

let ANGLE = `!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`;;

let ANGLE_REFL = `!A B. angle(A,A,B) = pi / &2 /\ angle(B,A,A) = pi / &2`;;

let ANGLE_REFL_MID = `!A B. ~(A = B) ==> angle(A,B,A) = &0`;;

let ANGLE_SYM = `!A B C. angle(A,B,C) = angle(C,B,A)`;;

let ANGLE_RANGE = `!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`;;

let COS_ANGLE_EQ = `!a b c a' b' c'.
        cos(angle(a,b,c)) = cos(angle(a',b',c')) <=>
        angle(a,b,c) = angle(a',b',c')`;;

let ANGLE_EQ = `!a b c a' b' c'.
        ~(a = b) /\ ~(c = b) /\ ~(a' = b') /\ ~(c' = b')
        ==> (angle(a,b,c) = angle(a',b',c') <=>
                ((a' - b') dot (c' - b')) * norm (a - b) * norm (c - b) =
                ((a - b) dot (c - b)) * norm (a' - b') * norm (c' - b'))`;;

let SIN_ANGLE_EQ_0 = `!A B C. sin(angle(A,B,C)) = &0 <=> angle(A,B,C) = &0 \/ angle(A,B,C) = pi`;;

let SIN_ANGLE_EQ = `!A B C A' B' C'. sin(angle(A,B,C)) = sin(angle(A',B',C')) <=>
                        angle(A,B,C) = angle(A',B',C') \/
                        angle(A,B,C) = pi - angle(A',B',C')`;;

let COLLINEAR_ANGLE = `!A B C. ~(A = B) /\ ~(B = C)
           ==> (collinear {A,B,C} <=> angle(A,B,C) = &0 \/ angle(A,B,C) = pi)`;;

let COLLINEAR_SIN_ANGLE = `!A B C. ~(A = B) /\ ~(B = C)
           ==> (collinear {A,B,C} <=> sin(angle(A,B,C)) = &0)`;;

let COLLINEAR_SIN_ANGLE_IMP = `!A B C. sin(angle(A,B,C)) = &0
           ==> ~(A = B) /\ ~(B = C) /\ collinear {A,B,C}`;;

let ANGLE_EQ_0_RIGHT = `!A B C. angle(A,B,C) = &0 ==> angle(A,B,D) = angle(C,B,D)`;;

let ANGLE_EQ_0_LEFT = `!A B C. angle(A,B,C) = &0 ==> angle(D,B,A) = angle(D,B,C)`;;

let ANGLE_EQ_PI_RIGHT = `!A B C. angle(A,B,C) = pi ==> angle(D,B,A) = pi - angle(D,B,C)`;;

let ANGLE_EQ_PI_LEFT = `!A B C. angle(A,B,C) = pi ==> angle(A,B,D) = pi - angle(C,B,D)`;;

let COS_ANGLE = `!a b c. cos(angle(a,b,c)) = if a = b \/ c = b then &0
                               else ((a - b) dot (c - b)) /
                                    (norm(a - b) * norm(c - b))`;;

let SIN_ANGLE = `!a b c. sin(angle(a,b,c)) =
             if a = b \/ c = b then &1
             else sqrt(&1 - (((a - b) dot (c - b)) /
                             (norm(a - b) * norm(c - b))) pow 2)`;;

let SIN_SQUARED_ANGLE = `!a b c. sin(angle(a,b,c)) pow 2 =
             if a = b \/ c = b then &1
             else &1 - (((a - b) dot (c - b)) /
                        (norm(a - b) * norm(c - b))) pow 2`;;

(* ------------------------------------------------------------------------- *)
(* The basic right angle triangles of elementary trigonometry.               *)
(* ------------------------------------------------------------------------- *)

let COS_ADJACENT_HYPOTENUSE = `!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> dist(A,C) * cos(angle(B,A,C)) = dist(A,B)`;;

let COS_ADJACENT_OVER_HYPOTENUSE = `!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> cos(angle(B,A,C)) = dist(A,B) / dist(A,C)`;;

let SIN_OPPOSITE_HYPOTENUSE = `!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> dist(A,C) * sin(angle(B,A,C)) = dist(C,B)`;;

let SIN_OPPOSITE_OVER_HYPOTENUSE = `!A B C:real^N.
        orthogonal (A - B) (C - B) /\ ~(A = C)
        ==> sin(angle(B,A,C)) = dist(C,B) / dist(A,C)`;;

let TAN_OPPOSITE_ADJACENT = `!A B C:real^N.
        orthogonal (A - B) (C - B) /\ ~(A = B)
        ==> dist(A,B) * tan(angle(B,A,C)) = dist(C,B)`;;

let TAN_OPPOSITE_OVER_ADJACENT = `!A B C:real^N.
        orthogonal (A - B) (C - B)
        ==> tan(angle(B,A,C)) = dist(C,B) / dist(A,B)`;;

(* ------------------------------------------------------------------------- *)
(* The law of cosines.                                                       *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_COSINES = `!A B C:real^N.
        dist(B,C) pow 2 = (dist(A,B) pow 2 + dist(A,C) pow 2) -
                          &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`;;

(* ------------------------------------------------------------------------- *)
(* The law of sines.                                                         *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_SINES = `!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)`;;

(* ------------------------------------------------------------------------- *)
(* The sum of the angles of a triangle.                                      *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_ANGLE_SUM_LEMMA = `!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1`;;

let COS_MINUS1_LEMMA = `!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi`;;

let TRIANGLE_ANGLE_SUM = `!A B C:real^N. ~(A = B /\ B = C /\ A = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi`;;

(* ------------------------------------------------------------------------- *)
(* A few more lemmas about angles.                                           *)
(* ------------------------------------------------------------------------- *)

let ANGLE_EQ_PI_OTHERS = `!A B C:real^N.
        angle(A,B,C) = pi
        ==> angle(B,C,A) = &0 /\ angle(A,C,B) = &0 /\
            angle(B,A,C) = &0 /\ angle(C,A,B) = &0`;;

let ANGLE_EQ_0_DIST = `!A B C:real^N. angle(A,B,C) = &0 <=>
                  ~(A = B) /\ ~(C = B) /\
                  (dist(A,B) = dist(A,C) + dist(C,B) \/
                   dist(B,C) = dist(A,C) + dist(A,B))`;;

let ANGLE_EQ_0_DIST_ABS = `!A B C:real^N. angle(A,B,C) = &0 <=>
                  ~(A = B) /\ ~(C = B) /\
                   dist(A,C) = abs(dist(A,B) - dist(C,B))`;;

(* ------------------------------------------------------------------------- *)
(* Some rules for congruent triangles (not necessarily in the same real^N).  *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_TRIANGLES_SSS = `!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        dist(B,C) = dist(B',C') /\
        dist(C,A) = dist(C',A')
        ==> angle(A,B,C) = angle(A',B',C')`;;

let CONGRUENT_TRIANGLES_SAS = `!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        angle(A,B,C) = angle(A',B',C') /\
        dist(B,C) = dist(B',C')
        ==> dist(A,C) = dist(A',C')`;;

let CONGRUENT_TRIANGLES_AAS = `!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        angle(B,C,A) = angle(B',C',A') /\
        dist(A,B) = dist(A',B') /\
        ~(collinear {A,B,C})
        ==> dist(A,C) = dist(A',C') /\ dist(B,C) = dist(B',C')`;;

let CONGRUENT_TRIANGLES_ASA = `!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        dist(A,B) = dist(A',B') /\
        angle(B,A,C) = angle(B',A',C') /\
        ~(collinear {A,B,C})
        ==> dist(A,C) = dist(A',C')`;;

(* ------------------------------------------------------------------------- *)
(* Full versions where we deduce everything from the conditions.             *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_TRIANGLES_SSS_FULL = `!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        dist(B,C) = dist(B',C') /\
        dist(C,A) = dist(C',A')
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`;;

let CONGRUENT_TRIANGLES_SAS_FULL = `!A B C:real^M A' B' C':real^N.
        dist(A,B) = dist(A',B') /\
        angle(A,B,C) = angle(A',B',C') /\
        dist(B,C) = dist(B',C')
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`;;

let CONGRUENT_TRIANGLES_AAS_FULL = `!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        angle(B,C,A) = angle(B',C',A') /\
        dist(A,B) = dist(A',B') /\
        ~(collinear {A,B,C})
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`;;

let CONGRUENT_TRIANGLES_ASA_FULL = `!A B C:real^M A' B' C':real^N.
        angle(A,B,C) = angle(A',B',C') /\
        dist(A,B) = dist(A',B') /\
        angle(B,A,C) = angle(B',A',C') /\
        ~(collinear {A,B,C})
        ==> dist(A,B) = dist(A',B') /\
            dist(B,C) = dist(B',C') /\
            dist(C,A) = dist(C',A') /\
            angle(A,B,C) = angle(A',B',C') /\
            angle(B,C,A) = angle(B',C',A') /\
            angle(C,A,B) = angle(C',A',B')`;;

(* ------------------------------------------------------------------------- *)
(* Between-ness.                                                             *)
(* ------------------------------------------------------------------------- *)

let ANGLE_BETWEEN = `!a b x. angle(a,x,b) = pi <=> ~(x = a) /\ ~(x = b) /\ between x (a,b)`;;

let BETWEEN_ANGLE = `!a b x. between x (a,b) <=> x = a \/ x = b \/ angle(a,x,b) = pi`;;

let ANGLES_ALONG_LINE = `!A B C D:real^N.
      ~(C = A) /\ ~(C = B) /\ between C (A,B)
      ==> angle(A,C,D) + angle(B,C,D) = pi`;;

let ANGLES_ADD_BETWEEN = `!A B C D:real^N.
        between C (A,B) /\ ~(D = A) /\ ~(D = B)
        ==> angle(A,D,C) + angle(C,D,B) = angle(A,D,B)`;;

(* ------------------------------------------------------------------------- *)
(* Distance from a point to a line expressed with angles.                    *)
(* ------------------------------------------------------------------------- *)

let SETDIST_POINT_LINE = `!x y z:real^N.
        setdist({x},affine hull {y,z}) = dist(x,y) * sin(angle(x,y,z))`;;

(* ------------------------------------------------------------------------- *)
(* A standard formula for the area of a triangle.                            *)
(* ------------------------------------------------------------------------- *)

let AREA_TRIANGLE_SIN = `!a b c:real^2.
     measure(convex hull {a,b,c}) =
     (dist(a,b) * dist(a,c) * sin(angle(b,a,c))) / &2`;;

(* ------------------------------------------------------------------------- *)
(* Angles satisfy the triangle law and hence vector_angle defines a metric.  *)
(* ------------------------------------------------------------------------- *)

let ANGLE_TRIANGLE_LAW = `!p u v w:real^N. angle(u,p,w) <= angle(u,p,v) + angle(v,p,w)`;;

let VECTOR_ANGLE_TRIANGLE_LAW = `!u v w:real^N. vector_angle u w <= vector_angle u v + vector_angle v w`;;
