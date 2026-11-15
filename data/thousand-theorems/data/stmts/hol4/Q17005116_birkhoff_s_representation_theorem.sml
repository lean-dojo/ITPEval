(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q17005116, "Birkhoff's representation theorem": the canonical map from a
  finite distributive lattice to the powerset of its sup-irreducible elements
  is an injective lattice homomorphism. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pred_setTheory;

val q17005116_finite_distributive_lattice_def = new_definition (
  "q17005116_finite_distributive_lattice_def",
  ``q17005116_finite_distributive_lattice
      (carrier : 'a -> bool)
      (le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a) <=>
      FINITE carrier /\
      (!x. carrier x ==> le_rel x x) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z /\
        le_rel x y /\ le_rel y z
        ==>
        le_rel x z) /\
      (!x y.
        carrier x /\ carrier y /\ le_rel x y /\ le_rel y x
        ==>
        x = y) /\
      (!x y.
        carrier x /\ carrier y
        ==>
        carrier (inf_op x y) /\ carrier (sup_op x y)) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z
        ==>
        (le_rel z (inf_op x y) <=> le_rel z x /\ le_rel z y)) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z
        ==>
        (le_rel (sup_op x y) z <=> le_rel x z /\ le_rel y z)) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z
        ==>
        inf_op x (sup_op y z) =
          sup_op (inf_op x y) (inf_op x z)) /\
      (!x y z.
        carrier x /\ carrier y /\ carrier z
        ==>
        sup_op x (inf_op y z) =
          inf_op (sup_op x y) (sup_op x z))``);

val q17005116_sup_irreducible_def = new_definition (
  "q17005116_sup_irreducible_def",
  ``q17005116_sup_irreducible
      (carrier : 'a -> bool)
      (le_rel : 'a -> 'a -> bool)
      (sup_op : 'a -> 'a -> 'a)
      (a : 'a) <=>
      carrier a /\
      ~(!x. carrier x ==> le_rel a x) /\
      (!b c.
        carrier b /\ carrier c /\ sup_op b c = a
        ==>
        b = a \/ c = a)``);

val q17005116_birkhoff_set_def = new_definition (
  "q17005116_birkhoff_set_def",
  ``q17005116_birkhoff_set
      (carrier : 'a -> bool)
      (le_rel : 'a -> 'a -> bool)
      (sup_op : 'a -> 'a -> 'a)
      (x : 'a)
      (a : 'a) <=>
      q17005116_sup_irreducible carrier le_rel sup_op a /\
      le_rel a x``);

val birkhoff_representation_theorem =
  ``!(carrier : 'a -> bool)
      (le_rel : 'a -> 'a -> bool)
      (inf_op : 'a -> 'a -> 'a)
      (sup_op : 'a -> 'a -> 'a).
      q17005116_finite_distributive_lattice
        carrier le_rel inf_op sup_op
      ==>
      (!x y a.
        carrier x /\ carrier y
        ==>
        (q17005116_birkhoff_set
            carrier le_rel sup_op (sup_op x y) a <=>
          q17005116_birkhoff_set carrier le_rel sup_op x a \/
          q17005116_birkhoff_set carrier le_rel sup_op y a)) /\
      (!x y a.
        carrier x /\ carrier y
        ==>
        (q17005116_birkhoff_set
            carrier le_rel sup_op (inf_op x y) a <=>
          q17005116_birkhoff_set carrier le_rel sup_op x a /\
          q17005116_birkhoff_set carrier le_rel sup_op y a)) /\
      (!x y.
        carrier x /\ carrier y /\
        (!a.
          q17005116_birkhoff_set carrier le_rel sup_op x a <=>
          q17005116_birkhoff_set carrier le_rel sup_op y a)
        ==>
        x = y)``;
