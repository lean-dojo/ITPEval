(*
  Statement-only formalization of the thousand-theorems corpus artifact Q1191709,
  "Egorov's theorem": an almost-everywhere convergent countable directed family
  of strongly measurable functions on a measurable set of finite measure
  converges uniformly outside a measurable subset of arbitrarily small measure.
  This file contains no proof.
*)

theory Q1191709_egorov_s_theorem
  imports "HOL-Analysis.Bochner_Integration"
begin

definition q1191709_pseudo_emetric ::
    "('b \<Rightarrow> 'b \<Rightarrow> ennreal) \<Rightarrow> bool" where
  "q1191709_pseudo_emetric edist \<longleftrightarrow>
    (\<forall>x. edist x x = 0) \<and>
    (\<forall>x y. edist x y = edist y x) \<and>
    (\<forall>x y z. edist x z \<le> edist x y + edist y z)"

definition q1191709_tendsto_at_top ::
    "('b \<Rightarrow> 'b \<Rightarrow> ennreal) \<Rightarrow>
      ('i::semilattice_sup \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> bool" where
  "q1191709_tendsto_at_top edist u y \<longleftrightarrow>
    (\<forall>\<delta> :: real. 0 < \<delta> \<longrightarrow>
      (\<exists>j. \<forall>k \<ge> j. edist (u k) y < ennreal \<delta>))"

definition q1191709_strongly_measurable ::
    "'a measure \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> ennreal) \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "q1191709_strongly_measurable M edist h \<longleftrightarrow>
    (\<exists>u :: nat \<Rightarrow> 'a \<Rightarrow> 'b.
      (\<forall>n. simple_function M (u n)) \<and>
      (\<forall>x \<in> space M.
        q1191709_tendsto_at_top edist (\<lambda>n. u n x) (h x)))"

definition q1191709_tendsto_uniformly_on ::
    "('b \<Rightarrow> 'b \<Rightarrow> ennreal) \<Rightarrow>
      ('i::semilattice_sup \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow>
      ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q1191709_tendsto_uniformly_on edist f g A \<longleftrightarrow>
    (\<forall>\<delta> :: real. 0 < \<delta> \<longrightarrow>
      (\<exists>j. \<forall>k \<ge> j. \<forall>x \<in> A.
        edist (f k x) (g x) < ennreal \<delta>))"

theorem egorov_s_theorem:
  fixes M :: "'a measure"
    and edist :: "'b \<Rightarrow> 'b \<Rightarrow> ennreal"
    and f :: "'i::{semilattice_sup,countable} \<Rightarrow> 'a \<Rightarrow> 'b"
    and g :: "'a \<Rightarrow> 'b"
    and s :: "'a set"
    and \<epsilon> :: real
  assumes pseudo_emetric:
      "q1191709_pseudo_emetric edist"
    and f_strongly_measurable:
      "\<And>n. q1191709_strongly_measurable M edist (f n)"
    and g_strongly_measurable:
      "q1191709_strongly_measurable M edist g"
    and s_measurable:
      "s \<in> sets M"
    and s_finite:
      "emeasure M s \<noteq> \<infinity>"
    and ae_tendsto:
      "AE x in M.
        x \<in> s \<longrightarrow>
          q1191709_tendsto_at_top edist (\<lambda>n. f n x) (g x)"
    and epsilon_pos:
      "0 < \<epsilon>"
  shows
      "\<exists>t \<subseteq> s.
        t \<in> sets M \<and>
        emeasure M t \<le> ennreal \<epsilon> \<and>
        q1191709_tendsto_uniformly_on edist f g (s - t)"
  sorry

end
