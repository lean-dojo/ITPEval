(* ========================================================================= *)
(* #61: Ceva's theorem.                                                      *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;
needs "Examples/sos.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* We use the notion of "betweenness".                                       *)
(* ------------------------------------------------------------------------- *)

let BETWEEN_THM = `between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b`;;

(* ------------------------------------------------------------------------- *)
(* Lemmas to reduce geometric concepts to more convenient forms.             *)
(* ------------------------------------------------------------------------- *)

let NORM_CROSS = `norm(a) * norm(b) * norm(c) = norm(d) * norm(e) * norm(f) <=>
   (a dot a) * (b dot b) * (c dot c) = (d dot d) * (e dot e) * (f dot f)`;;

let COLLINEAR = `!a b c:real^2.
        collinear {a:real^2,b,c} <=>
        ((a$1 - b$1) * (b$2 - c$2) = (a$2 - b$2) * (b$1 - c$1))`;;

(* ------------------------------------------------------------------------- *)
(* More or less automatic proof of the main direction.                       *)
(* ------------------------------------------------------------------------- *)

let CEVA_WEAK = `!A B C X Y Z P:real^2.
        ~(collinear {A,B,C}) /\
        between X (B,C) /\ between Y (A,C) /\ between Z (A,B) /\
        between P (A,X) /\ between P (B,Y) /\ between P (C,Z)
        ==> dist(B,X) * dist(C,Y) * dist(A,Z) =
            dist(X,C) * dist(Y,A) * dist(Z,B)`;;

(* ------------------------------------------------------------------------- *)
(* More laborious proof of equivalence.                                      *)
(* ------------------------------------------------------------------------- *)

let CEVA = `!A B C X Y Z:real^2.
        ~(collinear {A,B,C}) /\
        between X (B,C) /\ between Y (C,A) /\ between Z (A,B)
        ==> (dist(B,X) * dist(C,Y) * dist(A,Z) =
             dist(X,C) * dist(Y,A) * dist(Z,B) <=>
             (?P. between P (A,X) /\ between P (B,Y) /\ between P (C,Z)))`;;

(* ------------------------------------------------------------------------- *)
(* Just for geometric intuition, verify metrical version of "between".       *)
(* This isn't actually needed in the proof. Moreover, this is now actually   *)
(* the definition of "between" so this is all a relic.                       *)
(* ------------------------------------------------------------------------- *)

let BETWEEN_SYM = `!u v w. between v (u,w) <=> between v (w,u)`;;

let BETWEEN_METRICAL = `!u v w:real^N. between v (u,w) <=> dist(u,v) + dist(v,w) = dist(u,w)`;;
