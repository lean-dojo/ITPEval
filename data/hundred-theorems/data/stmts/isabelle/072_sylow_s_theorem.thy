(*  Title:      HOL/Algebra/Sylow.thy
    Author:     Florian Kammueller, with new proofs by L C Paulson
*)

theory Sylow
  imports Coset Exponent
begin

text \<open>See also \<^cite>\<open>"Kammueller-Paulson:1999"\<close>.\<close>

text \<open>The combinatorial argument is in theory \<open>Exponent\<close>.\<close>

lemma le_extend_mult: "\<lbrakk>0 < c; a \<le> b\<rbrakk> \<Longrightarrow> a \<le> b * c" for c :: nat
  by sorry

locale sylow = group +
  fixes p and a and m and calM and RelM
  assumes prime_p: "prime p"
    and order_G: "order G = (p^a) * m"
    and finite_G[iff]: "finite (carrier G)"
  defines "calM \<equiv> {s. s \<subseteq> carrier G \<and> card s = p^a}"
    and "RelM \<equiv> {(N1, N2). N1 \<in> calM \<and> N2 \<in> calM \<and> (\<exists>g \<in> carrier G. N1 = N2 #> g)}"
begin

lemma RelM_subset: "RelM \<subseteq> calM \<times> calM"
  by sorry

lemma RelM_refl_on: "refl_on calM RelM"
  by sorry

lemma RelM_sym: "sym RelM"
  by sorry

lemma RelM_trans: "trans RelM"
  by sorry

lemma RelM_equiv: "equiv calM RelM"
  by sorry

lemma M_subset_calM_prep: "M' \<in> calM // RelM  \<Longrightarrow> M' \<subseteq> calM"
  by sorry

end

subsection \<open>Main Part of the Proof\<close>

locale sylow_central = sylow +
  fixes H and M1 and M
  assumes M_in_quot: "M \<in> calM // RelM"
    and not_dvd_M: "\<not> (p ^ Suc (multiplicity p m) dvd card M)"
    and M1_in_M: "M1 \<in> M"
  defines "H \<equiv> {g. g \<in> carrier G \<and> M1 #> g = M1}"
begin

lemma M_subset_calM: "M \<subseteq> calM"
  by sorry

lemma card_M1: "card M1 = p^a"
  by sorry

lemma exists_x_in_M1: "\<exists>x. x \<in> M1"
  by sorry

lemma M1_subset_G [simp]: "M1 \<subseteq> carrier G"
  by sorry

lemma M1_inj_H: "\<exists>f \<in> H\<rightarrow>M1. inj_on f H"
  by sorry

end


subsection \<open>Discharging the Assumptions of \<open>sylow_central\<close>\<close>

context sylow
begin

lemma EmptyNotInEquivSet: "{} \<notin> calM // RelM"
  by sorry

lemma existsM1inM: "M \<in> calM // RelM \<Longrightarrow> \<exists>M1. M1 \<in> M"
  by sorry

lemma zero_less_o_G: "0 < order G"
  by sorry

lemma zero_less_m: "m > 0"
  by sorry

lemma card_calM: "card calM = (p^a) * m choose p^a"
  by sorry

lemma zero_less_card_calM: "card calM > 0"
  by sorry

lemma max_p_div_calM: "\<not> (p ^ Suc (multiplicity p m) dvd card calM)"
  by sorry

lemma finite_calM: "finite calM"
  by sorry

lemma lemma_A1: "\<exists>M \<in> calM // RelM. \<not> (p ^ Suc (multiplicity p m) dvd card M)"
  by sorry

end


subsubsection \<open>Introduction and Destruct Rules for \<open>H\<close>\<close>

context sylow_central
begin

lemma H_I: "\<lbrakk>g \<in> carrier G; M1 #> g = M1\<rbrakk> \<Longrightarrow> g \<in> H"
  by sorry

lemma H_into_carrier_G: "x \<in> H \<Longrightarrow> x \<in> carrier G"
  by sorry

lemma in_H_imp_eq: "g \<in> H \<Longrightarrow> M1 #> g = M1"
  by sorry

lemma H_m_closed: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
  by sorry

lemma H_not_empty: "H \<noteq> {}"
  by sorry

lemma H_is_subgroup: "subgroup H G"
  by sorry

lemma rcosetGM1g_subset_G: "\<lbrakk>g \<in> carrier G; x \<in> M1 #> g\<rbrakk> \<Longrightarrow> x \<in> carrier G"
  by sorry

lemma finite_M1: "finite M1"
  by sorry

lemma finite_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> finite (M1 #> g)"
  by sorry

lemma M1_cardeq_rcosetGM1g: "g \<in> carrier G \<Longrightarrow> card (M1 #> g) = card M1"
  by sorry

lemma M1_RelM_rcosetGM1g: 
  assumes "g \<in> carrier G"
  shows "(M1, M1 #> g) \<in> RelM"
  by sorry

end


subsection \<open>Equal Cardinalities of \<open>M\<close> and the Set of Cosets\<close>

text \<open>Injections between \<^term>\<open>M\<close> and \<^term>\<open>rcosets\<^bsub>G\<^esub> H\<close> show that
 their cardinalities are equal.\<close>

lemma ElemClassEquiv: "\<lbrakk>equiv A r; C \<in> A // r\<rbrakk> \<Longrightarrow> \<forall>x \<in> C. \<forall>y \<in> C. (x, y) \<in> r"
  by sorry

context sylow_central
begin

lemma M_elem_map: "M2 \<in> M \<Longrightarrow> \<exists>g. g \<in> carrier G \<and> M1 #> g = M2"
  by sorry

lemmas M_elem_map_carrier = M_elem_map [THEN someI_ex, THEN conjunct1]

lemmas M_elem_map_eq = M_elem_map [THEN someI_ex, THEN conjunct2]

lemma M_funcset_rcosets_H:
  "(\<lambda>x\<in>M. H #> (SOME g. g \<in> carrier G \<and> M1 #> g = x)) \<in> M \<rightarrow> rcosets H"
  by sorry

lemma inj_M_GmodH: "\<exists>f \<in> M \<rightarrow> rcosets H. inj_on f M"
  by sorry

end


subsubsection \<open>The Opposite Injection\<close>

context sylow_central
begin

lemma H_elem_map: "H1 \<in> rcosets H \<Longrightarrow> \<exists>g. g \<in> carrier G \<and> H #> g = H1"
  by sorry

lemmas H_elem_map_carrier = H_elem_map [THEN someI_ex, THEN conjunct1]

lemmas H_elem_map_eq = H_elem_map [THEN someI_ex, THEN conjunct2]

lemma rcosets_H_funcset_M:
  "(\<lambda>C \<in> rcosets H. M1 #> (SOME g. g \<in> carrier G \<and> H #> g = C)) \<in> rcosets H \<rightarrow> M"
  by sorry

lemma inj_GmodH_M: "\<exists>g \<in> rcosets H\<rightarrow>M. inj_on g (rcosets H)"
  by sorry

lemma calM_subset_PowG: "calM \<subseteq> Pow (carrier G)"
  by sorry


lemma finite_M: "finite M"
  by sorry

lemma cardMeqIndexH: "card M = card (rcosets H)"
  by sorry

lemma index_lem: "card M * card H = order G"
  by sorry

lemma card_H_eq: "card H = p^a"
  by sorry

end

lemma (in sylow) sylow_thm: "\<exists>H. subgroup H G \<and> card H = p^a"
  by sorry

text \<open>Needed because the locale's automatic definition refers to
  \<^term>\<open>semigroup G\<close> and \<^term>\<open>group_axioms G\<close> rather than
  simply to \<^term>\<open>group G\<close>.\<close>
lemma sylow_eq: "sylow G p a m \<longleftrightarrow> group G \<and> sylow_axioms G p a m"
  by sorry


subsection \<open>Sylow's Theorem\<close>

theorem sylow_thm:
  "\<lbrakk>prime p; group G; order G = (p^a) * m; finite (carrier G)\<rbrakk>
    \<Longrightarrow> \<exists>H. subgroup H G \<and> card H = p^a"
  by sorry

end
