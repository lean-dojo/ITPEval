(*
  Statement-only formalization of thousand-theorems corpus artifact Q1191319,
  "Radon–Nikodym theorem": under a Lebesgue decomposition of one measure
  relative to another, absolute continuity is equivalent to recovering the
  measure by weighting the reference measure with the density chosen from
  that decomposition. This file contains no proof.
*)

theory Q1191319_radon_nikodym_theorem
  imports "HOL-Analysis.Radon_Nikodym"
begin

definition q1191319_same_measurable_space ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "q1191319_same_measurable_space M N \<longleftrightarrow>
    sets M = sets N \<and> space M = UNIV \<and> space N = UNIV"

definition q1191319_mutually_singular ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "q1191319_mutually_singular M N \<longleftrightarrow>
    q1191319_same_measurable_space M N \<and>
    (\<exists>A \<in> sets M. emeasure M A = 0 \<and> emeasure N (- A) = 0)"

definition q1191319_decomposition_witness ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure \<Rightarrow>
      ('a \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "q1191319_decomposition_witness M N S f \<longleftrightarrow>
    q1191319_same_measurable_space M N \<and>
    q1191319_same_measurable_space M S \<and>
    f \<in> borel_measurable N \<and>
    q1191319_mutually_singular S N \<and>
    (\<forall>A \<in> sets N.
      emeasure M A = emeasure S A + emeasure (density N f) A)"

definition q1191319_has_lebesgue_decomposition ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "q1191319_has_lebesgue_decomposition M N \<longleftrightarrow>
    (\<exists>S f. q1191319_decomposition_witness M N S f)"

definition q1191319_rn_deriv ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a \<Rightarrow> ennreal" where
  "q1191319_rn_deriv M N =
    (if q1191319_has_lebesgue_decomposition M N
     then snd (SOME p.
       q1191319_decomposition_witness M N (fst p) (snd p))
     else (\<lambda>_. 0))"

theorem absolutely_continuous_iff_density_rn_deriv_eq:
  assumes "q1191319_has_lebesgue_decomposition M N"
  shows "absolutely_continuous N M \<longleftrightarrow>
    density N (q1191319_rn_deriv M N) = M"
  sorry

end
