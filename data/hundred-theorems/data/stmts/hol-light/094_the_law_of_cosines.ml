(* ========================================================================= *)
(* The law of cosines, of sines, and sum of angles of a triangle.            *)
(* ========================================================================= *)

needs "Multivariate/transcendentals.ml";;

prioritize_vector();;

(* ------------------------------------------------------------------------- *)
(* Angle between vectors (always 0 <= angle <= pi).                          *)
(* ------------------------------------------------------------------------- *)

let vangle = new_definition
 `vangle x y = if x = vec 0 \/ y = vec 0 then pi / &2
               else acs((x dot y) / (norm x * norm y))`;;

(* ------------------------------------------------------------------------- *)
(* Traditional geometric notion of angle (but always 0 <= theta <= pi).      *)
(* ------------------------------------------------------------------------- *)

let angle = new_definition
 `angle(a,b,c) = vangle (a - b) (c - b)`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas (more than we need for this result).                               *)
(* ------------------------------------------------------------------------- *)

let VANGLE = `!x y:real^N. x dot y = norm(x) * norm(y) * cos(vangle x y)`;;

let VANGLE_RANGE = `!x y:real^N. &0 <= vangle x y /\ vangle x y <= pi`;;

let ORTHOGONAL_VANGLE = `!x y:real^N. orthogonal x y <=> vangle x y = pi / &2`;;

let VANGLE_EQ_PI = `!x y:real^N. vangle x y = pi ==> norm(x) % y + norm(y) % x = vec 0`;;

let ANGLE_EQ_PI = `!A B C:real^N. angle(A,B,C) = pi ==> dist(A,C) = dist(A,B) + dist(B,C)`;;

let SIN_ANGLE_POS = `!A B C. &0 <= sin(angle(A,B,C))`;;

let ANGLE = `!A B C. (A - C) dot (B - C) = dist(A,C) * dist(B,C) * cos(angle(A,C,B))`;;

let ANGLE_REFL = `!A B. angle(A,A,B) = pi / &2 /\
         angle(B,A,A) = pi / &2`;;

let ANGLE_REFL_MID = `!A B. ~(A = B) ==> angle(A,B,A) = &0`;;

let ANGLE_SYM = `!A B C. angle(A,B,C) = angle(C,B,A)`;;

let ANGLE_RANGE = `!A B C. &0 <= angle(A,B,C) /\ angle(A,B,C) <= pi`;;

(* ------------------------------------------------------------------------- *)
(* The law of cosines.                                                       *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_COSINES = `!A B C:real^N.
     dist(B,C) pow 2 = dist(A,B) pow 2 + dist(A,C) pow 2 -
                         &2 * dist(A,B) * dist(A,C) * cos(angle(B,A,C))`;;

(* ------------------------------------------------------------------------- *)
(* The law of sines.                                                         *)
(* ------------------------------------------------------------------------- *)

let LAW_OF_SINES = `!A B C:real^N.
      sin(angle(A,B,C)) * dist(B,C) = sin(angle(B,A,C)) * dist(A,C)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the sum of the angles of a triangle.                                *)
(* ------------------------------------------------------------------------- *)

let TRIANGLE_ANGLE_SUM_LEMMA = `!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> cos(angle(B,A,C) + angle(A,B,C) + angle(B,C,A)) = -- &1`;;

let COS_MINUS1_LEMMA = `!x. cos(x) = -- &1 /\ &0 <= x /\ x < &3 * pi ==> x = pi`;;

let TRIANGLE_ANGLE_SUM = `!A B C:real^N. ~(A = B) /\ ~(A = C) /\ ~(B = C)
                  ==> angle(B,A,C) + angle(A,B,C) + angle(B,C,A) = pi`;;
