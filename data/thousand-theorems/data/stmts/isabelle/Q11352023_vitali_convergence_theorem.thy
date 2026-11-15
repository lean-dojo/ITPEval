(*
  Statement-only formalization of the thousand-theorems corpus artifact Q11352023,
  "Vitali convergence theorem": for a finite exponent at least one, convergence
  in measure together with uniform integrability and uniform tightness is
  equivalent to convergence in Lp on an arbitrary measure space.
  This file contains no proof.
*)

theory Q11352023_vitali_convergence_theorem
  imports "HOL-Analysis.Bochner_Integration"
begin

definition q11352023_normed_add_comm_group ::
    "('b::{ab_group_add,metric_space} \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q11352023_normed_add_comm_group bnorm \<longleftrightarrow>
      (\<forall>x. 0 \<le> bnorm x) \<and>
      (\<forall>x. bnorm x = 0 \<longleftrightarrow> x = 0) \<and>
      (\<forall>x y. bnorm (x + y) \<le> bnorm x + bnorm y) \<and>
      (\<forall>x y. dist x y = bnorm (x - y))"

definition q11352023_ae_strongly_measurable ::
    "'a measure \<Rightarrow> ('a \<Rightarrow> 'b::metric_space) \<Rightarrow> bool"
  where
    "q11352023_ae_strongly_measurable M h \<longleftrightarrow>
      (\<exists>s :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
        (\<forall>n. simple_function M (s n)) \<and>
        (AE x in M. (\<lambda>n. s n x) \<longlonglongrightarrow> h x))"

definition q11352023_eLpNorm ::
    "'a measure \<Rightarrow> ('b \<Rightarrow> real) \<Rightarrow> real \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> ennreal"
  where
    "q11352023_eLpNorm M bnorm p h =
      (let I = nn_integral M (\<lambda>x. ennreal (bnorm (h x) powr p))
       in if I = \<infinity> then \<infinity>
          else ennreal (enn2real I powr (1 / p)))"

definition q11352023_mem_Lp ::
    "'a measure \<Rightarrow> ('b::metric_space \<Rightarrow> real) \<Rightarrow> real \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q11352023_mem_Lp M bnorm p h \<longleftrightarrow>
      q11352023_ae_strongly_measurable M h \<and>
      q11352023_eLpNorm M bnorm p h < \<infinity>"

definition q11352023_outer_measure ::
    "'a measure \<Rightarrow> 'a set \<Rightarrow> ennreal"
  where
    "q11352023_outer_measure M A =
      Inf {emeasure M B | B. B \<in> sets M \<and> A \<subseteq> B}"

definition q11352023_tendsto_in_measure ::
    "'a measure \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b::metric_space) \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q11352023_tendsto_in_measure M f g \<longleftrightarrow>
      (\<forall>\<epsilon> :: real. 0 < \<epsilon> \<longrightarrow>
        (\<lambda>n. q11352023_outer_measure M
          {x. \<epsilon> \<le> dist (f n x) (g x)})
          \<longlonglongrightarrow> 0)"

definition q11352023_indicator ::
    "'a set \<Rightarrow> ('a \<Rightarrow> 'b::zero) \<Rightarrow> 'a \<Rightarrow> 'b"
  where
    "q11352023_indicator A h x = (if x \<in> A then h x else 0)"

definition q11352023_unif_integrable ::
    "'a measure \<Rightarrow> ('b::zero \<Rightarrow> real) \<Rightarrow> real \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q11352023_unif_integrable M bnorm p f \<longleftrightarrow>
      (\<forall>\<epsilon> :: real. 0 < \<epsilon> \<longrightarrow>
        (\<exists>\<delta> :: real. 0 < \<delta> \<and>
          (\<forall>n A. A \<in> sets M \<longrightarrow>
            emeasure M A \<le> ennreal \<delta> \<longrightarrow>
            q11352023_eLpNorm M bnorm p (q11352023_indicator A (f n))
              \<le> ennreal \<epsilon>)))"

definition q11352023_unif_tight ::
    "'a measure \<Rightarrow> ('b::zero \<Rightarrow> real) \<Rightarrow> real \<Rightarrow>
      (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
    "q11352023_unif_tight M bnorm p f \<longleftrightarrow>
      (\<forall>\<epsilon> :: real. 0 < \<epsilon> \<longrightarrow>
        (\<exists>A. q11352023_outer_measure M A \<noteq> \<infinity> \<and>
          (\<forall>n. q11352023_eLpNorm M bnorm p
            (q11352023_indicator (- A) (f n))
            \<le> ennreal \<epsilon>)))"

theorem vitali_convergence_theorem:
  fixes M :: "'a measure"
    and bnorm :: "'b::{ab_group_add,metric_space} \<Rightarrow> real"
    and p :: real
    and f :: "nat \<Rightarrow> 'a \<Rightarrow> 'b"
    and g :: "'a \<Rightarrow> 'b"
  assumes full_space:
      "space M = UNIV"
    and normed_group:
      "q11352023_normed_add_comm_group bnorm"
    and exponent:
      "1 \<le> p"
    and f_mem_Lp:
      "\<And>n. q11352023_mem_Lp M bnorm p (f n)"
    and g_mem_Lp:
      "q11352023_mem_Lp M bnorm p g"
  shows
      "q11352023_tendsto_in_measure M f g \<and>
        q11352023_unif_integrable M bnorm p f \<and>
        q11352023_unif_tight M bnorm p f
      \<longleftrightarrow>
        (\<lambda>n. q11352023_eLpNorm M bnorm p
          (\<lambda>x. f n x - g x)) \<longlonglongrightarrow> 0"
  sorry

end
