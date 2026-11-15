(*
  Statement-only formalization of Logipedia corpus artifact bool.bool_discr
  (catalog title "bool.bool_discr"): equality of two Boolean values selects
  an inhabited diagonal proposition in the Boolean discrimination matrix.
  This file contains no proof.
*)

From Stdlib Require Import Bool.Bool.

Theorem bool_bool_discr :
  forall x y : bool,
    x = y ->
    match x, y with
    | true, true => forall P : Prop, P -> P
    | true, false => forall P : Prop, P
    | false, true => forall P : Prop, P
    | false, false => forall P : Prop, P -> P
    end.
Admitted.
