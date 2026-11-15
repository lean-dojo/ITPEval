(*
  Statement-only formalization of thousand-theorems corpus artifact Q1052678,
  "Baire category theorem": in a Baire topological space, the intersection of
  any countable family of open dense sets is dense. This file contains no
  proof.
*)

theory Q1052678_baire_category_theorem
  imports "HOL.Topological_Spaces"
begin

definition dense_set :: "'a::topological_space set \<Rightarrow> bool" where
  "dense_set D \<longleftrightarrow>
    (\<forall>U. open U \<longrightarrow> U \<noteq> {} \<longrightarrow> U \<inter> D \<noteq> {})"

definition is_baire_space :: "'a::topological_space itself \<Rightarrow> bool" where
  "is_baire_space _ \<longleftrightarrow>
    (\<forall>f :: nat \<Rightarrow> 'a set.
      (\<forall>n. open (f n)) \<longrightarrow>
      (\<forall>n. dense_set (f n)) \<longrightarrow>
      dense_set (\<Inter>n. f n))"

theorem dense_sInter_of_isOpen:
  fixes S :: "'a::topological_space set set"
  assumes "is_baire_space TYPE('a)"
    and "\<And>s. s \<in> S \<Longrightarrow> open s"
    and "countable S"
    and "\<And>s. s \<in> S \<Longrightarrow> dense_set s"
  shows "dense_set (\<Inter>S)"
  sorry

end
