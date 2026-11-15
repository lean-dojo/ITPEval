(* Statement-only formalization of VERINA corpus artifact verina_advanced_42,
   catalog title "maxProfit": an executable scan computing the maximum profit
   from one purchase followed by one later sale, together with its indexed
   optimality and zero-profit correctness contract. This file contains no
   proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition maxProfit_precond (_prices : list nat) : Prop :=
  True.

Definition updateMinAndProfit
    (price minSoFar maxProfit : nat) : nat * nat :=
  let newMin := Nat.min minSoFar price in
  let profit :=
    if Nat.ltb minSoFar price
    then price - minSoFar
    else 0%nat in
  let newMaxProfit := Nat.max maxProfit profit in
  (newMin, newMaxProfit).

Fixpoint maxProfitAux
    (prices : list nat)
    (minSoFar maxProfit : nat) : nat :=
  match prices with
  | [] => maxProfit
  | price :: rest =>
      let '(newMin, newProfit) :=
        updateMinAndProfit price minSoFar maxProfit in
      maxProfitAux rest newMin newProfit
  end.

Definition maxProfit
    (prices : list nat)
    (_h_precond : maxProfit_precond prices) : nat :=
  match prices with
  | [] => 0%nat
  | price :: rest => maxProfitAux rest price 0%nat
  end.

Fixpoint maxProfit_zipIdxFrom
    (prices : list nat)
    (index : nat) : list (nat * nat) :=
  match prices with
  | [] => []
  | price :: rest =>
      (price, index) :: maxProfit_zipIdxFrom rest (S index)
  end.

Definition maxProfit_zipIdx
    (prices : list nat) : list (nat * nat) :=
  maxProfit_zipIdxFrom prices 0%nat.

Fixpoint maxProfit_pairwise
    {A : Type}
    (relation : A -> A -> Prop)
    (xs : list A) : Prop :=
  match xs with
  | [] => True
  | x :: rest =>
      Forall (relation x) rest /\
      maxProfit_pairwise relation rest
  end.

Definition maxProfit_noProfitableTransaction
    (indexed : list (nat * nat)) : bool :=
  forallb
    (fun buy =>
      let '(buyPrice, buyIndex) := buy in
      forallb
        (fun sell =>
          let '(sellPrice, sellIndex) := sell in
          orb
            (Nat.leb sellIndex buyIndex)
            (Nat.leb sellPrice buyPrice))
        indexed)
    indexed.

Definition maxProfit_achievesResult
    (indexed : list (nat * nat))
    (result : nat) : bool :=
  existsb
    (fun buy =>
      let '(buyPrice, buyIndex) := buy in
      existsb
        (fun sell =>
          let '(sellPrice, sellIndex) := sell in
          andb
            (Nat.ltb buyIndex sellIndex)
            (Nat.eqb (sellPrice - buyPrice) result))
        indexed)
    indexed.

Definition maxProfit_postcond
    (prices : list nat)
    (result : nat)
    (_h_precond : maxProfit_precond prices) : Prop :=
  let indexed := maxProfit_zipIdx prices in
  maxProfit_pairwise
    (fun buy sell =>
      let '(buyPrice, buyIndex) := buy in
      let '(sellPrice, sellIndex) := sell in
      (buyIndex < sellIndex)%nat ->
      (sellPrice - buyPrice <= result)%nat)
    indexed /\
  (result = 0%nat <->
    (length prices <= 1)%nat \/
    maxProfit_noProfitableTransaction indexed = true) /\
  ((result > 0)%nat ->
    maxProfit_achievesResult indexed result = true).

Theorem maxProfit_spec_satisfied
    (prices : list nat)
    (h_precond : maxProfit_precond prices) :
  maxProfit_postcond
    prices (maxProfit prices h_precond) h_precond.
Admitted.
