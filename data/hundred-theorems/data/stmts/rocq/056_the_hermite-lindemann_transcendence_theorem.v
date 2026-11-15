From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm ssralg poly ssrnum polydiv mxpoly ssrint rat.
From mathcomp Require Import polyorder finmap order.
From SsrMultinomials Require Import mpoly.
From Lindemann Require Import archi Rstruct Cstruct prelim.
From Lindemann Require Import Lind_part1 Lind_part2 Lind_part3.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope ring_scope.
Import GRing.Theory Num.Theory Archi.Theory Archi.Order.

Local Notation RtoC := Cstruct.RtoC.
Local Notation Cnat := Cstruct.Cnat.
Local Notation Cint := Cstruct.Cint.

Notation "x 'is_algebraic'" := (algebraicOver QtoC x)
  (at level 55).

Definition lin_indep_over (P : pred_class) {n : nat} (x : complexR ^ n) :=
  forall (lambda : complexR ^ n), lambda \in ffun_on P ->
    lambda != 0 -> \sum_(i < n) (lambda i * x i) != 0.

Definition alg_indep_over (P : pred_class) {n : nat} (x : complexR ^ n) :=
  forall (p : {mpoly complexR[n]}), p \is a mpolyOver _ P ->
    p != 0 -> p.@[x] != 0.

Local Notation setZroots := ((fset_roots Cint) : 
    complexR -> qualifier 1 {fset complexR}).




(******************************************************************************)
(*                          Lindemann's theorems                              *)
(******************************************************************************)

Theorem LindemannBaker : forall (l : nat) (alpha : complexR ^ l) (a : complexR ^ l),
  (0%N < l)%N -> injective alpha -> (forall i : 'I_l, alpha i is_algebraic) ->
  (forall i : 'I_l, a i != 0) -> (forall i : 'I_l, a i is_algebraic) ->
  (Cexp_span a alpha != 0).
Proof.
Admitted.

Theorem LindemannWeierstrass n (alpha : complexR ^ n) :
  (n > 0)%N -> (forall i : 'I_n, alpha i is_algebraic) ->
  lin_indep_over Cint alpha -> alg_indep_over Cint (finfun (Cexp \o alpha)).
Proof.
Admitted.

(* Print Assumptions LindemannWeierstrass *)






Lemma ffun1_lin_indep_over (P : pred_class) (x : complexR) :
  x != 0 -> lin_indep_over P (finfun (fun (i : 'I_1) => x)).
Proof.
Admitted.

Lemma ffun1_alg_indep_over (x : complexR) :
   (x is_algebraic) -> ~ (alg_indep_over Cint (finfun (fun (i : 'I_1) => x))).
Proof.
Admitted.




(******************************************************************************)
(*                          Hermite-Lindemann theorem                         *)
(******************************************************************************)

Theorem HermiteLindemann (x : complexR) :
  x != 0 -> x is_algebraic -> ~ ((Cexp x) is_algebraic).
Proof.
Admitted.

(* Print Assumptions HermiteLindemann *)




(******************************************************************************)
(*                          Transcendence of e                                *)
(******************************************************************************)

Theorem e_trans_by_LB :
  ~ (RtoC (Rtrigo_def.
Proof.
Admitted.

Theorem e_trans_by_LW :
  ~ (RtoC (Rtrigo_def.
Proof.
Admitted.

Theorem e_trans_by_HL :
  ~ (RtoC (Rtrigo_def.
Proof.
Admitted.




(******************************************************************************)
(*                          Transcendence of pi                               *)
(******************************************************************************)

Lemma eiPI_eqm1 : Cexp (RtoC Rtrigo1.
Proof.
Admitted.

Theorem Pi_trans_by_LB : ~ (RtoC Rtrigo1.
Proof.
Admitted.

Theorem Pi_trans_by_LW : ~ (RtoC Rtrigo1.
Proof.
Admitted.

Theorem Pi_trans_by_HL : ~ (RtoC Rtrigo1.
Proof.
Admitted.