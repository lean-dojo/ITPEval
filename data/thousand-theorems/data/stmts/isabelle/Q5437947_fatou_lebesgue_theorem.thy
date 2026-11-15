(*
  Statement-only formalization of the thousand-theorems corpus artifact Q5437947,
  "Fatou–Lebesgue theorem": Fatou's inequality for the lower Lebesgue integral
  of the pointwise liminf of a sequence of measurable extended-nonnegative
  functions. This file contains no proof.
*)

theory Q5437947_fatou_lebesgue_theorem
  imports "HOL-Analysis.Nonnegative_Lebesgue_Integration"
begin

theorem fatou_lebesgue_theorem:
  fixes M :: "'a measure"
    and f :: "nat \<Rightarrow> 'a \<Rightarrow> ennreal"
  assumes measurable:
      "\<And>n. f n \<in> borel_measurable M"
  shows
      "nn_integral M (\<lambda>x. liminf (\<lambda>n. f n x))
        \<le> liminf (\<lambda>n. nn_integral M (f n))"
  sorry

end
