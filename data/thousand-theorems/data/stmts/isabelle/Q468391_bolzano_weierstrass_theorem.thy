(*
  Statement-only formalization of the thousand-theorems corpus artifact Q468391
  (thousand-theorems__isabelle__Q468391), "Bolzano–Weierstrass theorem": in a
  proper pseudometric space, every sequence that is frequently contained in a
  bounded set, and hence every sequence contained in one, has a convergent
  strictly increasing subsequence whose limit lies in the set's closure. This
  file contains no proof.
*)

theory Q468391_bolzano_weierstrass_theorem
  imports Complex_Main
begin

definition q468391_pseudometric ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "q468391_pseudometric d \<longleftrightarrow>
    (\<forall>x y. 0 \<le> d x y) \<and>
    (\<forall>x. d x x = 0) \<and>
    (\<forall>x y. d x y = d y x) \<and>
    (\<forall>x y z. d x z \<le> d x y + d y z)"

definition q468391_open ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q468391_open d U \<longleftrightarrow>
    (\<forall>x \<in> U. \<exists>e > 0. \<forall>y. d x y < e \<longrightarrow> y \<in> U)"

definition q468391_compact ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q468391_compact d K \<longleftrightarrow>
    (\<forall>C.
      (\<forall>U \<in> C. q468391_open d U) \<longrightarrow>
      K \<subseteq> \<Union>C \<longrightarrow>
      (\<exists>D. D \<subseteq> C \<and> finite D \<and> K \<subseteq> \<Union>D))"

definition q468391_cball ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set" where
  "q468391_cball d x r = {y. d x y \<le> r}"

definition q468391_proper ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "q468391_proper d \<longleftrightarrow>
    (\<forall>x r. q468391_compact d (q468391_cball d x r))"

definition q468391_bounded ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "q468391_bounded d S \<longleftrightarrow>
    (\<exists>C. \<forall>x \<in> S. \<forall>y \<in> S. d x y \<le> C)"

definition q468391_closure ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "q468391_closure d S =
    {x. \<forall>e > 0. \<exists>y \<in> S. d x y < e}"

definition q468391_frequently_at_top ::
    "(nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "q468391_frequently_at_top P \<longleftrightarrow>
    (\<forall>N. \<exists>n \<ge> N. P n)"

definition q468391_strict_mono ::
    "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "q468391_strict_mono phi \<longleftrightarrow>
    (\<forall>m n. m < n \<longrightarrow> phi m < phi n)"

definition q468391_tends_to ::
    "('a \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow>
      (nat \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool" where
  "q468391_tends_to d u a \<longleftrightarrow>
    (\<forall>e > 0. \<exists>N. \<forall>n \<ge> N. d (u n) a < e)"

theorem tendsto_subseq_of_frequently_bounded:
  fixes d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
    and S :: "'a set"
    and x :: "nat \<Rightarrow> 'a"
  assumes pseudometric: "q468391_pseudometric d"
    and proper: "q468391_proper d"
    and bounded: "q468391_bounded d S"
    and frequently:
      "q468391_frequently_at_top (\<lambda>n. x n \<in> S)"
  shows "\<exists>a \<in> q468391_closure d S.
    \<exists>phi :: nat \<Rightarrow> nat.
      q468391_strict_mono phi \<and>
      q468391_tends_to d (x \<circ> phi) a"
  sorry

theorem tendsto_subseq_of_bounded:
  fixes d :: "'a \<Rightarrow> 'a \<Rightarrow> real"
    and S :: "'a set"
    and x :: "nat \<Rightarrow> 'a"
  assumes pseudometric: "q468391_pseudometric d"
    and proper: "q468391_proper d"
    and bounded: "q468391_bounded d S"
    and contained: "\<And>n. x n \<in> S"
  shows "\<exists>a \<in> q468391_closure d S.
    \<exists>phi :: nat \<Rightarrow> nat.
      q468391_strict_mono phi \<and>
      q468391_tends_to d (x \<circ> phi) a"
  sorry

end
