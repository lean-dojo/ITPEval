(*
  Statement-only formalization of Hundred Theorems artifact 025,
  "Schroeder-Bernstein Theorem": injections between two arbitrary sets in
  both directions imply that the sets are in bijection. This file contains
  no proof.
*)

let SCHROEDER_BERNSTEIN =
  `!s:A->bool t:B->bool f:A->B g:B->A.
      ((!x. x IN s ==> f x IN t) /\
       (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
       (!x. x IN t ==> g x IN s) /\
       (!x y. x IN t /\ y IN t /\ g x = g y ==> x = y))
      ==> ?h:A->B.
            (!x. x IN s ==> h x IN t) /\
            (!x y. x IN s /\ y IN s /\ h x = h y ==> x = y) /\
            (!y. y IN t ==> ?x. x IN s /\ h x = y)`;;
