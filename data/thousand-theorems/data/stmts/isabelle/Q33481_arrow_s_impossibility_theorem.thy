(*
  Statement-only formalization of the thousand-theorems corpus artifact Q33481
  (thousand-theorems__isabelle__Q33481), "Arrow's impossibility theorem": for
  a finite electorate and at least three alternatives, weak Pareto and
  independence of irrelevant alternatives force a social welfare function to
  be dictatorial. This file contains no proof.
*)

theory Q33481_arrow_s_impossibility_theorem
  imports Main
begin

definition q33481_preference_order :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "q33481_preference_order r \<longleftrightarrow>
    (\<forall>x. r x x) \<and>
    (\<forall>x y. r x y \<or> r y x) \<and>
    (\<forall>x y z. r x y \<longrightarrow> r y z \<longrightarrow> r x z)"

definition q33481_strict_preference ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "q33481_strict_preference r x y \<longleftrightarrow> r x y \<and> \<not> r y x"

definition q33481_valid_profile ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "q33481_valid_profile I R \<longleftrightarrow>
    (\<forall>i\<in>I. q33481_preference_order (R i)) \<and>
    (\<forall>i. i \<notin> I \<longrightarrow> R i = (\<lambda>x y. False))"

definition q33481_social_welfare_function ::
    "'i set \<Rightarrow>
      (('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      bool" where
  "q33481_social_welfare_function I F \<longleftrightarrow>
    (\<forall>R. q33481_valid_profile I R \<longrightarrow> q33481_preference_order (F R))"

definition q33481_same_pairwise_order ::
    "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "q33481_same_pairwise_order r s x y \<longleftrightarrow>
    (q33481_strict_preference r x y \<longleftrightarrow> q33481_strict_preference s x y) \<and>
    (q33481_strict_preference r y x \<longleftrightarrow> q33481_strict_preference s y x)"

definition q33481_weak_pareto ::
    "'i set \<Rightarrow> 'a set \<Rightarrow>
      (('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      bool" where
  "q33481_weak_pareto I A F \<longleftrightarrow>
    (\<forall>x\<in>A. \<forall>y\<in>A. \<forall>R.
      q33481_valid_profile I R \<longrightarrow>
      (\<forall>i\<in>I. q33481_strict_preference (R i) x y) \<longrightarrow>
      q33481_strict_preference (F R) x y)"

definition q33481_independence_of_irrelevant_alternatives ::
    "'i set \<Rightarrow> 'a set \<Rightarrow>
      (('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      bool" where
  "q33481_independence_of_irrelevant_alternatives I A F \<longleftrightarrow>
    (\<forall>R R'. q33481_valid_profile I R \<longrightarrow> q33481_valid_profile I R' \<longrightarrow>
      (\<forall>x\<in>A. \<forall>y\<in>A.
        (\<forall>i\<in>I. q33481_same_pairwise_order (R i) (R' i) x y) \<longrightarrow>
        q33481_same_pairwise_order (F R) (F R') x y))"

definition q33481_is_dictatorship ::
    "'i set \<Rightarrow> 'a set \<Rightarrow>
      (('i \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      bool" where
  "q33481_is_dictatorship I A F \<longleftrightarrow>
    (\<exists>i\<in>I. \<forall>x\<in>A. \<forall>y\<in>A. \<forall>R.
      q33481_valid_profile I R \<longrightarrow>
      q33481_strict_preference (R i) x y \<longrightarrow>
      q33481_strict_preference (F R) x y)"

theorem q33481_arrow_s_impossibility_theorem:
  assumes finite_voters: "finite I"
    and finite_alternatives: "finite A"
    and three_alternatives: "3 \<le> card A"
    and welfare_function: "q33481_social_welfare_function I F"
    and weak_pareto: "q33481_weak_pareto I A F"
    and independence: "q33481_independence_of_irrelevant_alternatives I A F"
  shows "q33481_is_dictatorship I A F"
  sorry

end
