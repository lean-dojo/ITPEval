(*
  Statement-only formalization of the thousand-theorems corpus artifact Q191693,
  "Lebesgue's decomposition theorem": an s-finite measure relative to a
  sigma-finite measure on the same arbitrary measurable space decomposes into
  a mutually singular measure and a measure given by a measurable ennreal
  density. This file contains no proof.
*)
theory Q191693_lebesgue_s_decomposition_theorem
  imports "HOL-Analysis.Radon_Nikodym"
begin

definition q191693_same_measurable_space ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "q191693_same_measurable_space M N \<longleftrightarrow>
    sets M = sets N \<and> space M = UNIV \<and> space N = UNIV"

definition q191693_s_finite :: "'a measure \<Rightarrow> bool" where
  "q191693_s_finite M \<longleftrightarrow>
    (\<exists>F :: nat \<Rightarrow> 'a measure.
      (\<forall>n. q191693_same_measurable_space M (F n) \<and>
        finite_measure (F n)) \<and>
      (\<forall>A \<in> sets M.
        emeasure M A = (\<Sum>n. emeasure (F n) A)))"

definition q191693_mutually_singular ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "q191693_mutually_singular M N \<longleftrightarrow>
    q191693_same_measurable_space M N \<and>
    (\<exists>A \<in> sets M. emeasure M A = 0 \<and> emeasure N (- A) = 0)"

definition q191693_decomposition_witness ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> 'a measure \<Rightarrow>
      ('a \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "q191693_decomposition_witness M N S f \<longleftrightarrow>
    q191693_same_measurable_space M N \<and>
    q191693_same_measurable_space M S \<and>
    f \<in> borel_measurable N \<and>
    q191693_mutually_singular S N \<and>
    (\<forall>A \<in> sets M.
      emeasure M A = emeasure S A + emeasure (density N f) A)"

definition have_lebesgue_decomposition_of_sigma_finite ::
    "'a measure \<Rightarrow> 'a measure \<Rightarrow> bool" where
  "have_lebesgue_decomposition_of_sigma_finite M N \<longleftrightarrow>
    (q191693_same_measurable_space M N \<longrightarrow>
      q191693_s_finite M \<longrightarrow>
      sigma_finite_measure N \<longrightarrow>
      (\<exists>S f. q191693_decomposition_witness M N S f))"

end
