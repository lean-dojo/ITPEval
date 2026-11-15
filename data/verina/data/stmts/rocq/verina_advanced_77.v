(* Statement-only formalization of VERINA corpus artifact verina_advanced_77,
   catalog title "trapRainWater": an executable two-pointer computation of
   trapped rainwater over natural-number elevations, together with the
   per-index maximum-height summation correctness contract. This file
   contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List.

Import ListNotations.

Definition trapRainWater_precond
    (_height : list nat) : Prop :=
  True.

Fixpoint trapLoop_fuel
    (fuel : nat)
    (height : list nat)
    (left right leftMax rightMax water : nat) : nat :=
  match fuel with
  | 0 => water
  | S fuel' =>
      if Nat.ltb left right
      then
        let hLeft := nth left height 0 in
        let hRight := nth right height 0 in
        if Nat.ltb hLeft hRight
        then
          if Nat.leb leftMax hLeft
          then
            trapLoop_fuel
              fuel' height (S left) right hLeft rightMax water
          else
            trapLoop_fuel
              fuel' height (S left) right leftMax rightMax
              (water + (leftMax - hLeft))
        else
          if Nat.leb rightMax hRight
          then
            trapLoop_fuel
              fuel' height left (right - 1) leftMax hRight water
          else
            trapLoop_fuel
              fuel' height left (right - 1) leftMax rightMax
              (water + (rightMax - hRight))
      else water
  end.

Definition trapLoop
    (height : list nat)
    (left right leftMax rightMax water : nat) : nat :=
  trapLoop_fuel
    (S (right - left))
    height left right leftMax rightMax water.

Definition trapRainWater
    (height : list nat)
    (_h_precond : trapRainWater_precond height) : nat :=
  trapLoop height 0 (length height - 1) 0 0 0.

Definition trapRainWater_postcond
    (height : list nat)
    (result : nat)
    (_h_precond : trapRainWater_precond height) : Prop :=
  let waterAt :=
    map
      (fun i =>
        let lmax :=
          fold_left Nat.max (firstn (i + 1) height) 0 in
        let rmax :=
          fold_left Nat.max (skipn i height) 0 in
        Nat.min lmax rmax - nth i height 0)
      (seq 0 (length height)) in
  result - fold_left Nat.add waterAt 0 = 0 /\
  fold_left Nat.add waterAt 0 <= result.

Theorem trapRainWater_spec_satisfied
    (height : list nat)
    (h_precond : trapRainWater_precond height) :
  trapRainWater_postcond
    height (trapRainWater height h_precond) h_precond.
Admitted.
