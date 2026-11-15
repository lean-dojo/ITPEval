(**
CoLoR, a Coq library on rewriting and termination.
See the COPYRIGHTS and LICENSE files.

- Frederic Blanqui, 2014-12-11

* Infinite Ramsey theorem

After "On a Problem of Formal Logic", F. P. Ramsey, London
Math. Soc. s2-30(1):264-286, 1930, doi:10.1112/plms/s2-30.1.264. *)

Set Implicit Arguments.

From Stdlib Require Import Morphisms Basics Setoid.
From CoLoR Require Import ClassicUtil IotaUtil EpsilonUtil DepChoice
     LogicUtil SetUtil FinSet InfSet NatUtil.

Section S.

  Variables (A : Type) (W : set A).

(****************************************************************************)
(** Infinite pigeon-hole principle with two holes. *)

  Lemma IPHP_with_2_holes (P : Pinf W) (f : elts P -> bool) :
    exists b (Q : Pinf P), forall x (i : mem x Q), f (elt (Pinf_sub Q _ i)) = b.
Proof.
Admitted.

  (* Let [i] be the function which maps [X] in [Pcard V n] to [add a X]
  in [Pcard P (S n)] provided that [a] is in [P] but not in [V]. *)
  Definition i n P (Q : Pinf P) (U : Pinf Q) V (a : A)
    (aU : mem a U) (VU_a : V [<=] rem a U) : Pcard V n -> Pcard P (S n).

  Proof.
Admitted.

  Arguments i [n P Q U V a] _ _ _.

  Lemma i_eq n P (Q : Pinf P) (U : Pinf Q) V (a : A)
        (VU_a : V [<=] rem a U) (aU : mem a U) (X : Pcard V n) :
    i aU VU_a X [=] add a X.
Proof.
Admitted.

  Arguments j n [P a T'] _ _ _ _.

  Lemma j_eq n (P : Pinf W) a (T' : Pinf W) (aP : mem a P) (naT : ~mem a T')
        (TP : T' [<=] P) X : j n aP naT TP X [=] add a X.
Proof.
Admitted.

  Theorem ramsey_with_2_colors : forall n (P : Pinf W)
    (f : Pcard P (S n) -> bool), Proper (Pcard_equiv ==> eq) f ->
    exists b (Q : Pinf P), forall X : Pcard Q (S n), f (Pcard_subset Q X) = b.
Proof.
Admitted.

End S.

Arguments ramsey_with_2_colors [A W n P f] _.

(****************************************************************************)
(** Ramsey theorem with a finite set of colors. *)

Theorem ramsey A (W : set A) n (P : Pinf W) B : forall (C : Pf B)
  (f : Pcard P (S n) -> elts C), Proper (Pcard_equiv ==> elts_eq) f ->
  exists c (Q : Pinf P), forall X : Pcard Q (S n), f (Pcard_subset Q X) = c.
Proof.
Admitted.
