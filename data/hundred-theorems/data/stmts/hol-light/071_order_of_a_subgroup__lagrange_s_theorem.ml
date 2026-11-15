(* ========================================================================= *)
(* Very trivial group theory, just to reach Lagrange theorem.                *)
(* NB: "Library/grouptheory.ml" has a more serious development of groups.    *)
(* ========================================================================= *)

loadt "Library/prime.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of what a group is.                                            *)
(* ------------------------------------------------------------------------- *)

let group = new_definition
  `group(g,( ** ),i,(e:A)) <=>
    (e IN g) /\ (!x. x IN g ==> i(x) IN g) /\
    (!x y. x IN g /\ y IN g ==> (x ** y) IN g) /\
    (!x y z. x IN g /\ y IN g /\ z IN g ==> (x ** (y ** z) = (x ** y) ** z)) /\
    (!x. x IN g ==> (x ** e = x) /\ (e ** x = x)) /\
    (!x. x IN g ==> (x ** i(x) = e) /\ (i(x) ** x = e))`;;

(* ------------------------------------------------------------------------- *)
(* Notion of a subgroup.                                                     *)
(* ------------------------------------------------------------------------- *)

let subgroup = new_definition
  `subgroup h (g,( ** ),i,(e:A)) <=> h SUBSET g /\ group(h,( ** ),i,e)`;;

(* ------------------------------------------------------------------------- *)
(* Lagrange theorem, introducing the coset representatives.                  *)
(* ------------------------------------------------------------------------- *)

let GROUP_LAGRANGE_COSETS = `!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> ?q. (CARD(g) = CARD(q) * CARD(h)) /\
                (!b. b IN g ==> ?a x. a IN q /\ x IN h /\ (b = a ** x))`;;

(* ------------------------------------------------------------------------- *)
(* Traditional statement is only part of this.                               *)
(* ------------------------------------------------------------------------- *)

let GROUP_LAGRANGE = `!g h ( ** ) i e.
        group (g,( ** ),i,e:A) /\ subgroup h (g,( ** ),i,e) /\ FINITE g
        ==> (CARD h) divides (CARD g)`;;
