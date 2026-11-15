(*
  The strong law of large numbers for independent, identically distributed
  integrable real random variables.  These are the two indexed statements
  from the retained probability-library development.
*)

Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms FiniteType List ListAdd Permutation infprod Almost NumberIso.
Require Import Sums SimpleExpectation PushNeg.
Require Import EquivDec Classical ClassicalChoice.
Require Import IndefiniteDescription ClassicalDescription.
Require Import BorelSigmaAlgebra utils.Utils ConditionalExpectation.
Require Import Independence sumtest Dynkin Measures.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Section StrongLaw.

Context {Ts : Type} {dom : SigmaAlgebra Ts} {Prts : ProbSpace dom}.

Lemma strong_law_zero_mean
    (X : nat -> Ts -> R)
    {rv : forall n, RandomVariable dom borel_sa (X n)}
    {isfe : forall n, IsFiniteExpectation Prts (X n)} :
  (forall n, FiniteExpectation Prts (X n) = 0) ->
  iid_rv_collection Prts borel_sa X ->
  almost Prts
    (fun omega =>
       is_lim_seq
         (fun n => (rvsum X n omega) / INR (S n))
         0).
Proof.
Admitted.

Lemma strong_law
    (X : nat -> Ts -> R) (mu : R)
    {rv : forall n, RandomVariable dom borel_sa (X n)}
    {isfe : forall n, IsFiniteExpectation Prts (X n)} :
  (forall n, FiniteExpectation Prts (X n) = mu) ->
  iid_rv_collection Prts borel_sa X ->
  almost Prts
    (fun omega =>
       is_lim_seq
         (fun n => (rvsum X n omega) / INR (S n))
         mu).
Proof.
Admitted.

End StrongLaw.
