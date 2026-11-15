(*
  Statement-only formalization of the thousand-theorems corpus artifact Q257387
  (thousand-theorems__isabelle__Q257387), "Vitali theorem": choosing one real
  from every equivalence class of [0,1] modulo rational differences produces a
  Vitali set that is not Lebesgue measurable. This file contains no proof.
*)

theory Q257387_vitali_theorem
  imports "HOL-Analysis.Lebesgue_Measure"
begin

definition q257387_unit_interval :: "real set"
  where "q257387_unit_interval = {0..1}"

definition q257387_rational_difference :: "real \<Rightarrow> real \<Rightarrow> bool"
  where
    "q257387_rational_difference x y \<longleftrightarrow>
      (\<exists>q :: rat. x - y = of_rat q)"

definition q257387_equivalence_class :: "real \<Rightarrow> real set"
  where
    "q257387_equivalence_class x =
      {y \<in> q257387_unit_interval. q257387_rational_difference y x}"

definition q257387_vitali_classes :: "real set set"
  where
    "q257387_vitali_classes =
      q257387_equivalence_class ` q257387_unit_interval"

definition q257387_vitali_representative :: "real set \<Rightarrow> real"
  where
    "q257387_vitali_representative C = (SOME x. x \<in> C)"

definition q257387_vitali_set :: "real set"
  where
    "q257387_vitali_set =
      q257387_vitali_representative ` q257387_vitali_classes"

theorem vitaliSet_not_measurable:
  "q257387_vitali_set \<notin> sets lborel"
  sorry

end
