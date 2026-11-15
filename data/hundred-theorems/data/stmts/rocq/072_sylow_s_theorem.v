(*
  Sylow's theorems, expressed with MathComp's finite-group API.  Importing
  the maintained library avoids duplicating its implementation while keeping
  the existence, conjugacy, counting, and congruence claims explicit.
*)

From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope group_scope.

Section SylowStatements.

Variables (p : nat) (gT : finGroupType) (G : {group gT}).

Theorem sylow_theorem_statement :
  [/\ forall P, [max P | p.-subgroup(G) P] = p.-Sylow(G) P,
      [transitive G, on 'Syl_p(G) | 'JG],
      forall P, p.-Sylow(G) P -> #|'Syl_p(G)| = #|G : 'N_G(P)|
    & prime p -> #|'Syl_p(G)| %% p = 1%N].
Proof.
exact: Sylow's_theorem.
Qed.

Theorem sylow_exists_statement :
  {P : {group gT} | p.-Sylow(G) P}.
Proof.
exact: Sylow_exists.
Qed.

Theorem sylow_conjugacy_statement (P Q : {group gT}) :
  p.-Sylow(G) P ->
  p.-Sylow(G) Q ->
  exists2 x, x \in G & Q :=: P :^ x.
Proof.
exact: Sylow_trans.
Qed.

Theorem sylow_count_statement (P : {group gT}) :
  p.-Sylow(G) P ->
  #|'Syl_p(G)| = #|G : 'N_G(P)|.
Proof.
exact: card_Syl.
Qed.

Theorem sylow_congruence_statement :
  prime p ->
  #|'Syl_p(G)| %% p = 1%N.
Proof.
exact: card_Syl_mod.
Qed.

End SylowStatements.
