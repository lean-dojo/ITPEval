(*
  Statement-only formalization of Thousand Theorems corpus artifact Q17005116,
  "Birkhoff's representation theorem": every finite distributive lattice
  embeds by a lattice homomorphism into the powerset of its sup-irreducible
  elements. This file contains no proof.
*)

let q17005116_is_finite_distributive_lattice = new_definition
  `q17005116_is_finite_distributive_lattice
      (carrier:A->bool) (le_rel:A->A->bool)
      (inf_op:A->A->A) (sup_op:A->A->A) <=>
     FINITE carrier /\
     (!x. x IN carrier ==> le_rel x x) /\
     (!x y z.
        x IN carrier /\ y IN carrier /\ z IN carrier /\
        le_rel x y /\ le_rel y z
        ==> le_rel x z) /\
     (!x y.
        x IN carrier /\ y IN carrier /\ le_rel x y /\ le_rel y x
        ==> x = y) /\
     (!x y.
        x IN carrier /\ y IN carrier
        ==> inf_op x y IN carrier /\ sup_op x y IN carrier) /\
     (!x y z.
        x IN carrier /\ y IN carrier /\ z IN carrier
        ==> (le_rel z (inf_op x y) <=> le_rel z x /\ le_rel z y)) /\
     (!x y z.
        x IN carrier /\ y IN carrier /\ z IN carrier
        ==> (le_rel (sup_op x y) z <=> le_rel x z /\ le_rel y z)) /\
     (!x y z.
        x IN carrier /\ y IN carrier /\ z IN carrier
        ==> inf_op x (sup_op y z) =
            sup_op (inf_op x y) (inf_op x z)) /\
     (!x y z.
        x IN carrier /\ y IN carrier /\ z IN carrier
        ==> sup_op x (inf_op y z) =
            inf_op (sup_op x y) (sup_op x z))`;;

let q17005116_sup_irreducible = new_definition
  `q17005116_sup_irreducible carrier le_rel sup_op a <=>
     a IN carrier /\
     ~(!x. x IN carrier ==> le_rel a x) /\
     (!b c.
        b IN carrier /\ c IN carrier /\ sup_op b c = a
        ==> b = a \/ c = a)`;;

let Q17005116_BIRKHOFF_REPRESENTATION =
  `!(carrier:A->bool) (le_rel:A->A->bool)
    (inf_op:A->A->A) (sup_op:A->A->A).
      q17005116_is_finite_distributive_lattice
        carrier le_rel inf_op sup_op
      ==> ?birkhoff:A->A->bool.
            (!x a.
               x IN carrier
               ==> (birkhoff x a <=>
                    q17005116_sup_irreducible
                      carrier le_rel sup_op a /\
                    le_rel a x)) /\
            (!x y a.
               x IN carrier /\ y IN carrier
               ==> (birkhoff (sup_op x y) a <=>
                    birkhoff x a \/ birkhoff y a)) /\
            (!x y a.
               x IN carrier /\ y IN carrier
               ==> (birkhoff (inf_op x y) a <=>
                    birkhoff x a /\ birkhoff y a)) /\
            (!x y.
               x IN carrier /\ y IN carrier /\
               (!a. birkhoff x a <=> birkhoff y a)
               ==> x = y)`;;
