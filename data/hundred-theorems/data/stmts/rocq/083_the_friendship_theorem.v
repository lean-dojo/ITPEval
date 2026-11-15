From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Friendship.combinatorics.
Require Import Friendship.statement_reduction.


(* Longer version *)
Theorem Friendship'
  (T: finType) (T_nonempty: [set: T] != set0)
  (F (* friendship relation *): rel T) (Fsym: symmetric F) (Firr: irreflexive F)
  (Co: T -> T -> T) (Col: forall u v : T, u != v -> F u (Co u v))
  (Cor: forall u v : T, u != v -> F v (Co u v))
  (CoUnique: forall u v w : T, u != v -> F u w -> F v w -> w = Co u v):
  {u : T | forall v : T, u != v -> F u v}.
Proof.
Admitted.

  
(* Shorter version *)
Theorem Friendship
  (T: finType) (T_nonempty: [set: T] != set0)
  (F (* friendship relation *): rel T) (Fsym: symmetric F) (Firr: irreflexive F) :

  (* u!= v have exactly 1 common friend *)
  (forall (u v: T), u != v -> #|[set w | F u w & F v w]| == 1) ->
  {u : T | forall v : T, u != v -> F u v}.
Proof.
Admitted.
