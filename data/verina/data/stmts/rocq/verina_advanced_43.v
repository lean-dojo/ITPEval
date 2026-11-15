(* Statement-only formalization of VERINA corpus artifact verina_advanced_43,
   catalog title "maxStrength": executable enumeration of every nonempty
   index-selected subset of an integer list and computation of its maximum
   product, together with its membership and maximality correctness contract.
   This file contains no proof. *)

From Stdlib Require Import Bool.Bool Lists.List ZArith.

Import ListNotations.
Open Scope Z_scope.

Definition maxStrength_precond (nums : list Z) : Prop :=
  nums <> [].

Fixpoint maxStrength_addHeadChoices
    (x : Z)
    (subsets : list (list Z)) : list (list Z) :=
  match subsets with
  | [] => []
  | subset :: remaining =>
      subset :: (x :: subset) ::
        maxStrength_addHeadChoices x remaining
  end.

Fixpoint maxStrength_powerSet
    (nums : list Z) : list (list Z) :=
  match nums with
  | [] => [[]]
  | x :: rest =>
      maxStrength_addHeadChoices x (maxStrength_powerSet rest)
  end.

Definition maxStrength_nonempty (subset : list Z) : bool :=
  match subset with
  | [] => false
  | _ :: _ => true
  end.

Definition maxStrength_product (subset : list Z) : Z :=
  fold_left Z.mul subset 1.

Definition maxStrength_products (nums : list Z) : list Z :=
  map maxStrength_product
    (filter maxStrength_nonempty (maxStrength_powerSet nums)).

Fixpoint maxStrength_maxOption (products : list Z) : option Z :=
  match products with
  | [] => None
  | product :: remaining =>
      match maxStrength_maxOption remaining with
      | None => Some product
      | Some currentMax => Some (Z.max product currentMax)
      end
  end.

Definition maxStrength
    (nums : list Z)
    (_h_precond : maxStrength_precond nums) : Z :=
  match maxStrength_maxOption (maxStrength_products nums) with
  | Some maximum => maximum
  | None => -1000000
  end.

Definition maxStrength_postcond
    (nums : list Z)
    (result : Z)
    (_h_precond : maxStrength_precond nums) : Prop :=
  let products := maxStrength_products nums in
  existsb (Z.eqb result) products = true /\
  forallb (fun product => Z.leb product result) products = true.

Theorem maxStrength_spec_satisfied
    (nums : list Z)
    (h_precond : maxStrength_precond nums) :
  maxStrength_postcond
    nums (maxStrength nums h_precond) h_precond.
Admitted.
