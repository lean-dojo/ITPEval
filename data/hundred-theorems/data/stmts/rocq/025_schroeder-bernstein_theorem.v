(* Contribution to the Coq Library   V6.3 (July 1999)                       *)
(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.11                                 *)
(*                              Feb 2nd 1996                                *)
(*                                                                          *)
(*                (notations and layout updated March 2009)                 *)
(****************************************************************************)
(*                               Schroeder.v                                *)
(****************************************************************************)
(* This file is distributed under the terms of the                          *) 
(* GNU Lesser General Public License Version 2.1                            *)
(****************************************************************************)


(**  If A is of cardinal less than B and conversely, then A and B           *)
(**  are equipollent                                                        *)
(**  In other words, if there is an injective map from A to B and           *)
(**  an injective map from B to A then there exists a map from A onto B.    *)

(**                  (based on a proof by Fraenkel)                         *)

Require Import Ensembles.      (* Ensemble, In, Included, Setminus *)
Require Import Relations_1.    (* Relation, Transitive *)
Require Import Powerset.       (* Inclusion_is_transitive *)
Require Import Classical_Prop. (* classic *)

Require Import Setminus_fact.
Require Import Sums.
Require Import Functions.
Require Import Equipollence.

Section Schroeder_Bernstein.


(****************************************************************************)
(** We need the decidability of the belonging relation on sets              *)
(** This is equivalent to classical logic                                   *)

Definition in_or_not_in (U : Type) (x : U) (A : Ensemble U) :=
  classic (In U A x).


(****************************************************************************)
(**  A and B are sets of elements in the univers U                          *)


Variable U : Type.

Let SU := Ensemble U.

Variable A B : SU.  (* A and B are sets of elements in the univers U *)


  Section Bijection.

  (**************************************************************************)
  (** We now show that if f and g are injections resp from A to B and from  *)
  (** B to A, then there is a subset J of A s.t. h, defined to be f on A    *)
  (** and the converse of g on A\J is a bijection from A to B               *)

  Variable f g : Relation U.  (* f and g are relations *)

  Hypothesis f_inj : injection U A B f. (* f and g are injections *)
  Hypothesis g_inj : injection U B A g.

  Let Imf : Ensemble U -> Ensemble U := Im U f.
  Let Img : Ensemble U -> Ensemble U := Im U g.

  (** Constructing J s.t. g(B\f(J))=A\J *)

    (** (Setminus U A C) denotes the difference A\C         *)
    (** (Included U A C) means that A is included in C  *)

    Let F (C : SU) := Setminus U A (Img (Setminus U B (Imf C))).

    Let D (C : SU) := Included U C (F C).

    Let J := Set_Sum U D.


  (**  We show that so-built J is the subset we are looking for *)

    (** J is Tarski's fix-point of F, a function which is growing *)
    (** w.r.t. inclusion                                          *)

    (** Lemma: F is growing *)

      Lemma F_growing :
       forall C C' : SU, Included U C C' -> Included U (F C) (F C').
Proof.
Admitted.

  End Bijection.


(**    Schroeder-Bernstein-Cantor Theorem     *)

Theorem Schroeder : A <=_card B -> B <=_card A -> A =_card B.
Proof.
Admitted.


End Schroeder_Bernstein.


                           (* The end *)


(* $Id$ *)
