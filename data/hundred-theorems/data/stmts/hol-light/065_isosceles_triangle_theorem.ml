(* ========================================================================= *)
(* Isosceles triangle theorem.                                               *)
(* ========================================================================= *)

needs "Multivariate/geom.ml";;

(* ------------------------------------------------------------------------- *)
(* The theorem, according to Wikipedia.                                      *)
(* ------------------------------------------------------------------------- *)

let ISOSCELES_TRIANGLE_THEOREM = `!A B C:real^N. dist(A,C) = dist(B,C) ==> angle(C,A,B) = angle(A,B,C)`;;

(* ------------------------------------------------------------------------- *)
(* The obvious converse.                                                     *)
(* ------------------------------------------------------------------------- *)

let ISOSCELES_TRIANGLE_CONVERSE = `!A B C:real^N. angle(C,A,B) = angle(A,B,C) /\ ~(collinear {A,B,C})
                  ==> dist(A,C) = dist(B,C)`;;

(* ------------------------------------------------------------------------- *)
(* Some other equivalents sometimes called the ITT (see the Web page         *)
(* http://www.sonoma.edu/users/w/wilsonst/Courses/Math_150/Theorems/itt.html *)
(* ------------------------------------------------------------------------- *)

let lemma = `!A B C D:real^N.
        between D (A,B)
        ==> (orthogonal (A - B) (C - D) <=>
                angle(A,D,C) = pi / &2 /\ angle(B,D,C) = pi / &2)`;;

let ISOSCELES_TRIANGLE_1 = `!A B C D:real^N.
        dist(A,C) = dist(B,C) /\ D = midpoint(A,B)
        ==> angle(A,C,D) = angle(B,C,D)`;;

let ISOSCELES_TRIANGLE_2 = `!A B C D:real^N.
        between D (A,B) /\
        dist(A,C) = dist(B,C) /\ angle(A,C,D) = angle(B,C,D)
        ==> orthogonal (A - B) (C - D)`;;

let ISOSCELES_TRIANGLE_3 = `!A B C D:real^N.
        between D (A,B) /\
        dist(A,C) = dist(B,C) /\ orthogonal (A - B) (C - D)
        ==> D = midpoint(A,B)`;;

(* ------------------------------------------------------------------------- *)
(* Now the converses to those as well.                                       *)
(* ------------------------------------------------------------------------- *)

let ISOSCELES_TRIANGLE_4 = `!A B C D:real^N.
        D = midpoint(A,B) /\ orthogonal (A - B) (C - D)
        ==> dist(A,C) = dist(B,C)`;;

let ISOSCELES_TRIANGLE_5 = `!A B C D:real^N.
        ~collinear{D,C,A} /\ between D (A,B) /\
        angle(A,C,D) = angle(B,C,D) /\ orthogonal (A - B) (C - D)
        ==> dist(A,C) = dist(B,C)`;;

let ISOSCELES_TRIANGLE_6 = `!A B C D:real^N.
        ~collinear{D,C,A} /\ D = midpoint(A,B) /\ angle(A,C,D) = angle(B,C,D)
        ==> dist(A,C) = dist(B,C)`;;
