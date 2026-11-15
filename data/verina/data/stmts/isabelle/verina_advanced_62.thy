(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_62,
  catalog title "rain": a deterministic two-pointer program computes trapped
  rainwater over a list of nonnegative integer heights, together with its
  prefix/suffix-maximum postcondition and correctness contract. This file
  contains no proof.
*)

theory verina_advanced_62
  imports Main
begin

definition rain_precond :: "int list \<Rightarrow> bool" where
  "rain_precond heights \<longleftrightarrow>
    list_all (\<lambda>h. h \<ge> 0) heights"

fun rain_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "rain_getBang [] i = 0"
| "rain_getBang (h # heights) 0 = h"
| "rain_getBang (h # heights) (Suc i) = rain_getBang heights i"

fun rain_aux ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int" where
  "rain_aux 0 heights left right leftMax rightMax water = water"
| "rain_aux (Suc fuel) heights left right leftMax rightMax water =
    (if left \<ge> right
     then water
     else if rain_getBang heights left \<le> rain_getBang heights right
     then
       (let newLeftMax = max leftMax (rain_getBang heights left);
            newWater =
              water + max 0 (leftMax - rain_getBang heights left)
        in rain_aux fuel heights (left + 1) right
             newLeftMax rightMax newWater)
     else
       (let newRightMax = max rightMax (rain_getBang heights right);
            newWater =
              water + max 0 (rightMax - rain_getBang heights right)
        in rain_aux fuel heights left (right - 1)
             leftMax newRightMax newWater))"

definition rain :: "int list \<Rightarrow> int" where
  "rain heights =
    (if length heights < 3
     then 0
     else
       (let n = length heights
        in rain_aux (n - 1) heights 0 (n - 1)
             (rain_getBang heights 0)
             (rain_getBang heights (n - 1)) 0))"

fun rain_max_left_loop ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "rain_max_left_loop 0 heights j maxSoFar = maxSoFar"
| "rain_max_left_loop (Suc fuel) heights j maxSoFar =
    rain_max_left_loop fuel heights (j + 1)
      (max maxSoFar (rain_getBang heights j))"

definition rain_max_left_at :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "rain_max_left_at heights i =
    rain_max_left_loop (i + 1) heights 0 0"

fun rain_max_right_loop ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "rain_max_right_loop 0 heights j maxSoFar = maxSoFar"
| "rain_max_right_loop (Suc fuel) heights j maxSoFar =
    rain_max_right_loop fuel heights (j + 1)
      (max maxSoFar (rain_getBang heights j))"

definition rain_max_right_at :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "rain_max_right_at heights i =
    rain_max_right_loop (length heights - i) heights i 0"

definition rain_water_at :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "rain_water_at heights i =
    max 0
      (min (rain_max_left_at heights i) (rain_max_right_at heights i) -
        rain_getBang heights i)"

fun rain_sum_water_loop ::
    "nat \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "rain_sum_water_loop 0 heights i acc = acc"
| "rain_sum_water_loop (Suc fuel) heights i acc =
    rain_sum_water_loop fuel heights (i + 1)
      (acc + rain_water_at heights i)"

definition rain_sum_water :: "int list \<Rightarrow> int" where
  "rain_sum_water heights =
    rain_sum_water_loop (length heights) heights 0 0"

definition rain_postcond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "rain_postcond heights result \<longleftrightarrow>
    result \<ge> 0 \<and>
    (if length heights < 3
     then result = 0
     else result = rain_sum_water heights)"

theorem rain_spec_satisfied:
  assumes "rain_precond heights"
  shows "rain_postcond heights (rain heights)"
  sorry

end
