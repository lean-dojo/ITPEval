(* Statement-only formalization of VERINA corpus artifact verina_basic_30,
   catalog title "elementWiseModulo": executable element-wise Euclidean
   remainder of two equal-length nonempty integer arrays with nonzero
   divisors, together with length and pointwise correctness. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Lists.List ZArith.

Import ListNotations.

Definition lean_int_emod (x y : Z) : Z :=
  Z.modulo x (Z.abs y).

Definition elementWiseModulo_precond
    (a b : list Z) : Prop :=
  length a = length b /\
  (0 < length a)%nat /\
  forall i : nat,
    (i < length b)%nat ->
    nth i b 0%Z <> 0%Z.

Fixpoint elementWiseModulo_mapIdxFrom
    (a b : list Z) (i : nat) : list Z :=
  match a with
  | [] => []
  | x :: rest =>
      lean_int_emod x (nth i b 0%Z) ::
      elementWiseModulo_mapIdxFrom rest b (S i)
  end.

Definition elementWiseModulo
    (a b : list Z)
    (_h_precond : elementWiseModulo_precond a b) : list Z :=
  elementWiseModulo_mapIdxFrom a b 0%nat.

Definition elementWiseModulo_postcond
    (a b result : list Z)
    (_h_precond : elementWiseModulo_precond a b) : Prop :=
  length result = length a /\
  forall i : nat,
    (i < length result)%nat ->
    nth i result 0%Z =
      lean_int_emod (nth i a 0%Z) (nth i b 0%Z).

Theorem elementWiseModulo_spec_satisfied
    (a b : list Z)
    (h_precond : elementWiseModulo_precond a b) :
  elementWiseModulo_postcond
    a b (elementWiseModulo a b h_precond) h_precond.
Admitted.
