(* ========================================================================= *)
(* #55: Theorem on product of segments of chords.                            *)
(* ========================================================================= *)

needs "Multivariate/convex.ml";;

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Geometric concepts.                                                       *)
(* ------------------------------------------------------------------------- *)

let BETWEEN_THM = `between x (a,b) <=>
       ?u. &0 <= u /\ u <= &1 /\ x = u % a + (&1 - u) % b`;;

let length = new_definition
 `length(A:real^2,B:real^2) = norm(B - A)`;;

(* ------------------------------------------------------------------------- *)
(* One more special reduction theorem to avoid square roots.                 *)
(* ------------------------------------------------------------------------- *)

let lemma = `!x y. &0 <= x /\ &0 <= y ==> (x pow 2 = y pow 2 <=> x = y)`;;

let NORM_CROSS = `norm(a) * norm(b) = norm(c) * norm(d) <=>
   (a dot a) * (b dot b) = (c dot c) * (d dot d)`;;

(* ------------------------------------------------------------------------- *)
(* Now the main theorem.                                                     *)
(* ------------------------------------------------------------------------- *)

let SEGMENT_CHORDS = `!centre radius q r s t b.
        between b (q,r) /\ between b (s,t) /\
        length(q,centre) = radius /\ length(r,centre) = radius /\
        length(s,centre) = radius /\ length(t,centre) = radius
        ==> length(q,b) * length(b,r) = length(s,b) * length(b,t)`;;
