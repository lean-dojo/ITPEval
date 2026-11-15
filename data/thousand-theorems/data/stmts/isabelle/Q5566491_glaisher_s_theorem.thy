(*
  Statement-only formalization of thousand-theorems corpus artifact Q5566491
  (thousand-theorems__isabelle__Q5566491), "Glaisher's theorem": for a
  positive modulus, the number of partitions of a natural number into parts
  not divisible by that modulus equals the number in which every part occurs
  fewer than that modulus many times. This file contains no proof.
*)

theory Q5566491_glaisher_s_theorem
  imports Main
begin

definition q5566491_partitions :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "q5566491_partitions n =
    {P. P 0 = 0 \<and>
      (\<forall>k. n < k \<longrightarrow> P k = 0) \<and>
      (\<Sum>k\<in>{1..n}. k * P k) = n}"

definition q5566491_restricted :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "q5566491_restricted n m =
    {P \<in> q5566491_partitions n. \<forall>k. 0 < P k \<longrightarrow> \<not> m dvd k}"

definition q5566491_count_restricted ::
    "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) set" where
  "q5566491_count_restricted n m =
    {P \<in> q5566491_partitions n. \<forall>k. P k < m}"

theorem q5566491_glaisher:
  fixes n m :: nat
  assumes "0 < m"
  shows "card (q5566491_restricted n m) =
    card (q5566491_count_restricted n m)"
  sorry

end
