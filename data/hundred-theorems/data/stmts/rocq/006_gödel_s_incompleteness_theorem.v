From Coq Require Import Ensembles.
From Coq Require Import List.
From Coq Require Import Arith.
From hydras.Ackermann Require Import folProp.
From hydras.Ackermann Require Import folProof.
From hydras.Ackermann Require Import subProp.
From hydras.Ackermann Require Import ListExt.
From Goedel Require Import fixPoint codeSysPrf.
From hydras.Ackermann Require Import wConsistent.
From hydras.Ackermann Require Import NN.
From hydras.Ackermann Require Import code.
From hydras.Ackermann Require Import checkPrf.
From hydras Require Import Compat815.

From LibHyps Require Export LibHyps.
From hydras Require Export MoreLibHyps NewNotations.

Import NNnotations codeNatToTerm.


(* TO do: remove this kind of redefinition *)
Definition codeFNN := codeFormula (cl:=LcodeLNN) .

(* cf Gilles' paper ? *)
Notation reflection f := (natToTerm (codeFNN f)).
  
Section Goedel's_1st_Incompleteness.

Variable T : System.

Hypothesis extendsNN : Included _ NN T.

(*
 There exists a formula repT 
  -  with only a free variable v0
  -  which means "v0 is a term which reflects some axiom of T"

   (see also codeSysPrf.v)
*)
Variable repT : Formula.
Variable v0 : nat.
Hypothesis
  freeVarRepT : forall v : nat, In v (freeVarF repT) -> v = v0.

Hypothesis
  expressT1 :
    forall f : Formula, mem _ T f ->
    SysPrf T (substF repT v0 (reflection f)).

Hypothesis
  expressT2 :
    forall f : Formula, ~ mem _ T f ->
    SysPrf T (~ (substF repT v0 (reflection f)))%fol.




Definition codeSysPrf :=
  codeSysPrf LNN LcodeLNN codeArityLNTF codeArityLNNR
    codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition codeSysPf :=
  codeSysPf LNN LcodeLNN codeArityLNTF codeArityLNNR
    codeArityLNTFIsPR codeArityLNNRIsPR repT v0.

Definition G := let (a,_) := FixPointLNN (notH codeSysPf) 0 in a.


Definition codeSysPfCorrect :=
  codeSysPfCorrect LNN LcodeLNN codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT1.

Definition codeSysPrfCorrect2 :=
  codeSysPrfCorrect2 LNN LcodeLNN codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNNRIsPR
    codeArityLNNRIsCorrect1 T extendsNN T repT v0 freeVarRepT expressT2.

Definition codeSysPrfCorrect3 :=
  codeSysPrfCorrect3 LNN LcodeLNN codeArityLNTF
    codeArityLNNR codeArityLNTFIsPR codeArityLNTFIsCorrect1
    codeArityLNTFIsCorrect2 codeArityLNNRIsPR codeArityLNNRIsCorrect1
    codeArityLNNRIsCorrect2  T extendsNN.
 


Lemma freeVarG : closed G.
Proof.
Admitted.

Lemma FirstIncompletenessA : SysPrf T G -> Inconsistent LNN T.
Proof.
Admitted.

(*I don't believe I can prove

 (SysPrf T (notH G))->(wInconsistent T))
 
 So instead I prove: *)

Lemma FirstIncompletenessB :
  wConsistent T -> ~ SysPrf T (notH G).
Proof.
Admitted.


Theorem Goedel'sIncompleteness1st :
 wConsistent T ->
 exists f : Formula, independent T f /\ closed f.
Proof.
Admitted.

End Goedel's_1st_Incompleteness.


