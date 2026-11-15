(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4950096
  (thousand-theorems__rocq__Q4950096), "Bourbaki–Witt theorem": every
  inflationary endofunction on a nonempty chain-complete partial order has a
  fixed point. This file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Record q4950096_nonempty_chain
    (A : Type) (le : A -> A -> Prop) : Type := {
  q4950096_chain_carrier : A -> Prop;
  q4950096_chain_nonempty :
    exists x : A, q4950096_chain_carrier x;
  q4950096_chain_comparable :
    forall x y : A,
      q4950096_chain_carrier x ->
      q4950096_chain_carrier y ->
      x <> y ->
      le x y \/ le y x
}.

Arguments q4950096_nonempty_chain A le : clear implicits.
Arguments q4950096_chain_carrier {A le} _ _.

Record q4950096_chain_complete_partial_order
    (A : Type) : Type := {
  q4950096_le : A -> A -> Prop;
  q4950096_le_refl :
    forall x : A, q4950096_le x x;
  q4950096_le_trans :
    forall x y z : A,
      q4950096_le x y ->
      q4950096_le y z ->
      q4950096_le x z;
  q4950096_le_antisym :
    forall x y : A,
      q4950096_le x y ->
      q4950096_le y x ->
      x = y;
  q4950096_cSup :
    q4950096_nonempty_chain A q4950096_le -> A;
  q4950096_le_cSup :
    forall (c : q4950096_nonempty_chain A q4950096_le)
           (x : A),
      q4950096_chain_carrier c x ->
      q4950096_le x (q4950096_cSup c);
  q4950096_cSup_le :
    forall (c : q4950096_nonempty_chain A q4950096_le)
           (x : A),
      (forall y : A,
        q4950096_chain_carrier c y ->
        q4950096_le y x) ->
      q4950096_le (q4950096_cSup c) x
}.

Arguments q4950096_le {A} _ _ _.
Arguments q4950096_cSup {A} _ _.

Module ChainCompletePartialOrder.

Theorem nonempty_fixedPoints_of_inflationary :
  forall (A : Type)
         (O : q4950096_chain_complete_partial_order A)
         (f : A -> A),
    (exists inhabitant : A, True) ->
    (forall x : A, q4950096_le O x (f x)) ->
    exists x : A, f x = x.
Admitted.

End ChainCompletePartialOrder.
