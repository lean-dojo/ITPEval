(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_77,
  catalog title "trapRainWater": an executable two-pointer program computes
  trapped rain water from a list of natural-number elevations, together with
  its precondition, exact water-sum postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_advanced_77
  imports Main
begin

definition trapRainWater_getBang ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "trapRainWater_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition trapRainWater_precond :: "nat list \<Rightarrow> bool" where
  "trapRainWater_precond height \<longleftrightarrow> True"

partial_function (tailrec) trapLoop ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat" where
  "trapLoop height left right leftMax rightMax water =
    (if left < right then
       let hLeft = trapRainWater_getBang height left;
           hRight = trapRainWater_getBang height right
       in
         if hLeft < hRight then
           let updated =
             (if leftMax \<le> hLeft
              then (hLeft, water)
              else (leftMax, water + (leftMax - hLeft)))
           in trapLoop height (left + 1) right
                (fst updated) rightMax (snd updated)
         else
           let updated =
             (if rightMax \<le> hRight
              then (hRight, water)
              else (rightMax, water + (rightMax - hRight)))
           in trapLoop height left (right - 1)
                leftMax (fst updated) (snd updated)
     else water)"

definition trapRainWater :: "nat list \<Rightarrow> nat" where
  "trapRainWater height =
    trapLoop height 0 (length height - 1) 0 0 0"

definition trapRainWater_waterAt :: "nat list \<Rightarrow> nat list" where
  "trapRainWater_waterAt height =
    map
      (\<lambda>i.
        let lmax = foldl max 0 (take (i + 1) height);
            rmax = foldl max 0 (drop i height)
        in min lmax rmax - trapRainWater_getBang height i)
      [0..<length height]"

definition trapRainWater_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "trapRainWater_postcond height result \<longleftrightarrow>
    (let total = foldl (+) 0 (trapRainWater_waterAt height)
     in result - total = 0 \<and> total \<le> result)"

theorem trapRainWater_spec_satisfied:
  assumes "trapRainWater_precond height"
  shows "trapRainWater_postcond height (trapRainWater height)"
  sorry

end
