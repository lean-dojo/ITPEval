(* Statement-only formalization of VERINA corpus artifact verina_basic_104,
   catalog title "update_map": an executable right-biased merge of two
   list-backed integer maps followed by stable sorting by key, together with
   its uniqueness precondition, lookup-based postcondition, and final
   correctness proposition. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List Sorting.Sorted ZArith.

Import ListNotations.
Open Scope Z_scope.

Record Map (K V : Type) : Type := {
  entries : list (K * V)
}.

Arguments entries {K V} _.

Definition empty {K V : Type} : Map K V :=
  {| entries := [] |}.

Definition pair_beq {K V : Type}
    (key_eqb : K -> K -> bool)
    (value_eqb : V -> V -> bool)
    (p1 p2 : K * V) : bool :=
  andb
    (key_eqb (fst p1) (fst p2))
    (value_eqb (snd p1) (snd p2)).

Fixpoint list_beq {A : Type}
    (element_eqb : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      andb (element_eqb x y) (list_beq element_eqb xs' ys')
  | _, _ => false
  end.

Definition map_beq {K V : Type}
    (key_eqb : K -> K -> bool)
    (value_eqb : V -> V -> bool)
    (m1 m2 : Map K V) : bool :=
  andb
    (Nat.eqb (length (entries m1)) (length (entries m2)))
    (list_beq (pair_beq key_eqb value_eqb)
      (entries m1) (entries m2)).

Definition insert {K V : Type}
    (key_eqb : K -> K -> bool)
    (m : Map K V)
    (k : K)
    (v : V) : Map K V :=
  {| entries :=
       filter
         (fun p => negb (key_eqb (fst p) k))
         (entries m) ++ [(k, v)] |}.

Fixpoint find_value {K V : Type}
    (key_eqb : K -> K -> bool)
    (xs : list (K * V))
    (k : K) : option V :=
  match xs with
  | [] => None
  | p :: rest =>
      if key_eqb (fst p) k
      then Some (snd p)
      else find_value key_eqb rest k
  end.

Definition update_map_find
    (m : Map Z Z)
    (k : Z) : option Z :=
  find_value Z.eqb (entries m) k.

Definition update_map_precond
    (m1 m2 : Map Z Z) : Prop :=
  NoDup (map fst (entries m1)) /\
  NoDup (map fst (entries m2)).

Definition update_map_fold_entry
    (acc : Map Z Z)
    (entry : Z * Z) : Map Z Z :=
  insert Z.eqb acc (fst entry) (snd entry).

Fixpoint update_map_merge_fuel
    (fuel : nat)
    (left right : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => left ++ right
  | S fuel' =>
      match left, right with
      | [], _ => right
      | _, [] => left
      | x :: xs, y :: ys =>
          if Z.leb (fst x) (fst y)
          then x :: update_map_merge_fuel fuel' xs (y :: ys)
          else y :: update_map_merge_fuel fuel' (x :: xs) ys
      end
  end.

Definition update_map_merge
    (left right : list (Z * Z)) : list (Z * Z) :=
  update_map_merge_fuel
    (length left + length right)%nat left right.

Fixpoint update_map_mergeSort_fuel
    (fuel : nat)
    (xs : list (Z * Z)) : list (Z * Z) :=
  match fuel with
  | O => xs
  | S fuel' =>
      match xs with
      | [] => []
      | [x] => [x]
      | _ :: _ :: _ =>
          let split_point := Nat.div (S (length xs)) 2 in
          update_map_merge
            (update_map_mergeSort_fuel
              fuel' (firstn split_point xs))
            (update_map_mergeSort_fuel
              fuel' (skipn split_point xs))
      end
  end.

Definition update_map_mergeSort
    (xs : list (Z * Z)) : list (Z * Z) :=
  update_map_mergeSort_fuel (length xs) xs.

Definition update_map
    (m1 m2 : Map Z Z)
    (_h_precond : update_map_precond m1 m2) : Map Z Z :=
  let updated :=
    fold_left update_map_fold_entry (entries m2) m1 in
  {| entries := update_map_mergeSort (entries updated) |}.

Definition option_Z_eqb
    (x y : option Z) : bool :=
  match x, y with
  | Some a, Some b => Z.eqb a b
  | None, None => true
  | _, _ => false
  end.

Definition update_map_postcond
    (m1 m2 result : Map Z Z)
    (_h_precond : update_map_precond m1 m2) : Prop :=
  StronglySorted
    (fun a b => (fst a <= fst b)%Z)
    (entries result) /\
  forallb
    (fun x =>
      option_Z_eqb
        (update_map_find result (fst x))
        (Some (snd x)))
    (entries m2) = true /\
  forallb
    (fun x =>
      match update_map_find m2 (fst x) with
      | Some _ => true
      | None =>
          option_Z_eqb
            (update_map_find result (fst x))
            (Some (snd x))
      end)
    (entries m1) = true /\
  forallb
    (fun x =>
      match update_map_find m1 (fst x) with
      | Some v =>
          match update_map_find m2 (fst x) with
          | Some v' => Z.eqb (snd x) v'
          | None => Z.eqb (snd x) v
          end
      | None =>
          option_Z_eqb
            (update_map_find m2 (fst x))
            (Some (snd x))
      end)
    (entries result) = true.

Theorem update_map_spec_satisfied
    (m1 m2 : Map Z Z)
    (h_precond : update_map_precond m1 m2) :
  update_map_postcond
    m1 m2 (update_map m1 m2 h_precond) h_precond.
Admitted.
