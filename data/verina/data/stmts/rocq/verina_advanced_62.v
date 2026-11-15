(* Statement-only formalization of VERINA corpus artifact verina_advanced_62,
   catalog title "rain": an executable two-pointer computation of trapped
   rainwater over nonnegative integer heights, together with its prefix- and
   suffix-maximum correctness contract. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat Bool.Bool Lists.List ZArith.

Import ListNotations.

Definition rain_precond (heights : list Z) : Prop :=
  forallb (fun height => Z.leb 0 height) heights = true.

Fixpoint rain_aux_fuel
    (fuel left right : nat)
    (leftMax rightMax water : Z)
    (heights : list Z) : Z :=
  match fuel with
  | O => water
  | S fuel' =>
      if Nat.leb right left
      then water
      else
        let leftHeight := nth left heights 0%Z in
        let rightHeight := nth right heights 0%Z in
        if Z.leb leftHeight rightHeight
        then
          let newLeftMax := Z.max leftMax leftHeight in
          let newWater :=
            (water + Z.max 0 (leftMax - leftHeight))%Z in
          rain_aux_fuel
            fuel' (S left) right newLeftMax rightMax newWater heights
        else
          let newRightMax := Z.max rightMax rightHeight in
          let newWater :=
            (water + Z.max 0 (rightMax - rightHeight))%Z in
          rain_aux_fuel
            fuel' left (Nat.pred right) leftMax newRightMax newWater heights
  end.

Definition rain
    (heights : list Z)
    (_h_precond : rain_precond heights) : Z :=
  if Nat.ltb (length heights) 3
  then 0%Z
  else
    let n := length heights in
    let right := Nat.pred n in
    rain_aux_fuel
      (Nat.sub right 0)
      0 right
      (nth 0 heights 0%Z)
      (nth right heights 0%Z)
      0%Z heights.

Fixpoint rain_max_left_fuel
    (fuel i j : nat)
    (max_so_far : Z)
    (heights : list Z) : Z :=
  match fuel with
  | O => max_so_far
  | S fuel' =>
      if Nat.ltb i j
      then max_so_far
      else
        rain_max_left_fuel
          fuel' i (S j)
          (Z.max max_so_far (nth j heights 0%Z))
          heights
  end.

Definition rain_max_left_at
    (heights : list Z)
    (i : nat) : Z :=
  rain_max_left_fuel (S i) i 0 0%Z heights.

Fixpoint rain_max_right_fuel
    (fuel j : nat)
    (max_so_far : Z)
    (heights : list Z) : Z :=
  match fuel with
  | O => max_so_far
  | S fuel' =>
      if Nat.leb (length heights) j
      then max_so_far
      else
        rain_max_right_fuel
          fuel' (S j)
          (Z.max max_so_far (nth j heights 0%Z))
          heights
  end.

Definition rain_max_right_at
    (heights : list Z)
    (i : nat) : Z :=
  rain_max_right_fuel
    (Nat.sub (length heights) i) i 0%Z heights.

Definition rain_water_at
    (heights : list Z)
    (i : nat) : Z :=
  Z.max 0
    (Z.min
      (rain_max_left_at heights i)
      (rain_max_right_at heights i) -
     nth i heights 0%Z).

Fixpoint rain_sum_water_fuel
    (fuel i : nat)
    (accumulator : Z)
    (heights : list Z) : Z :=
  match fuel with
  | O => accumulator
  | S fuel' =>
      if Nat.leb (length heights) i
      then accumulator
      else
        rain_sum_water_fuel
          fuel' (S i)
          (accumulator + rain_water_at heights i)%Z
          heights
  end.

Definition rain_total_by_maxima (heights : list Z) : Z :=
  rain_sum_water_fuel (length heights) 0 0%Z heights.

Definition rain_postcond
    (heights : list Z)
    (result : Z)
    (_h_precond : rain_precond heights) : Prop :=
  (0 <= result)%Z /\
  if Nat.ltb (length heights) 3
  then result = 0%Z
  else result = rain_total_by_maxima heights.

Theorem rain_spec_satisfied
    (heights : list Z)
    (h_precond : rain_precond heights) :
  rain_postcond heights (rain heights h_precond) h_precond.
Admitted.
