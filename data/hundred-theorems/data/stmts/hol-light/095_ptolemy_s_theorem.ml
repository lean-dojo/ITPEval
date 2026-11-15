(* ========================================================================= *)
(* Ptolemy's theorem.                                                        *)
(* ========================================================================= *)

needs "Multivariate/transcendentals.ml";;

(* ------------------------------------------------------------------------- *)
(* Some 2-vector special cases.                                              *)
(* ------------------------------------------------------------------------- *)

let DOT_VECTOR = `(vector [x1;y1] :real^2) dot (vector [x2;y2]) = x1 * x2 + y1 * y2`;;

(* ------------------------------------------------------------------------- *)
(* Lemma about distance between points with polar coordinates.               *)
(* ------------------------------------------------------------------------- *)

let DIST_SEGMENT_LEMMA = `!a1 a2. &0 <= a1 /\ a1 <= a2 /\ a2 <= &2 * pi /\ &0 <= radius
           ==> dist(centre + radius % vector [cos(a1);sin(a1)] :real^2,
                    centre + radius % vector [cos(a2);sin(a2)]) =
               &2 * radius *  sin((a2 - a1) / &2)`;;

(* ------------------------------------------------------------------------- *)
(* Hence the overall theorem.                                                *)
(* ------------------------------------------------------------------------- *)

let PTOLEMY = `!A B C D:real^2 a b c d centre radius.
        A = centre + radius % vector [cos(a);sin(a)] /\
        B = centre + radius % vector [cos(b);sin(b)] /\
        C = centre + radius % vector [cos(c);sin(c)] /\
        D = centre + radius % vector [cos(d);sin(d)] /\
        &0 <= radius /\
        &0 <= a /\ a <= b /\ b <= c /\ c <= d /\ d <= &2 * pi
        ==> dist(A,C) * dist(B,D) =
            dist(A,B) * dist(C,D) + dist(A,D) * dist(B,C)`;;
