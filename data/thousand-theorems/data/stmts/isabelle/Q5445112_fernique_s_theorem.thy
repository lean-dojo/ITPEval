(*
  Statement-only formalization of the thousand-theorems corpus artifact Q5445112,
  (thousand-theorems__isabelle__Q5445112), "Fernique's theorem": every Gaussian
  measure on a complete second-countable real normed vector space admits a positive
  constant for which the exponential of that constant times the squared norm is
  integrable. This file contains no proof.
*)

theory Q5445112_fernique_s_theorem
  imports "HOL-Analysis.Bochner_Integration"
begin

definition q5445112_is_gaussian ::
    "'a::real_normed_vector measure \<Rightarrow> bool"
  where
    "q5445112_is_gaussian M \<longleftrightarrow>
      sets M = sets (borel :: 'a measure) \<and>
      (\<forall>L :: 'a \<Rightarrow> real.
        bounded_linear L \<longrightarrow>
        (\<exists>m variance :: real.
          0 \<le> variance \<and>
          (\<forall>t :: real.
            integral\<^sup>L M (\<lambda>x. cos (t * L x)) =
              exp (-(variance * t ^ 2) / 2) * cos (t * m) \<and>
            integral\<^sup>L M (\<lambda>x. sin (t * L x)) =
              exp (-(variance * t ^ 2) / 2) * sin (t * m))))"

theorem fernique_s_theorem:
  fixes M ::
    "'a::{real_normed_vector, complete_space, second_countable_topology} measure"
  assumes "q5445112_is_gaussian M"
  shows "\<exists>C :: real.
    0 < C \<and> integrable M (\<lambda>x. exp (C * norm x ^ 2))"
  sorry

end
