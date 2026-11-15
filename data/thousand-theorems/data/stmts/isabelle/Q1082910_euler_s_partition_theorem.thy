(*
  Statement-only formalization of thousand-theorems corpus artifact Q1082910,
  "Euler's partition theorem": for every natural number, the number of its
  partitions into odd parts equals the number of its partitions into distinct
  parts. This file contains no proof.
*)

theory Q1082910_euler_s_partition_theorem
  imports Main
begin

definition nat_partition :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "nat_partition n p \<longleftrightarrow>
    (\<forall>i. p i \<noteq> 0 \<longrightarrow> 1 \<le> i \<and> i \<le> n) \<and>
    (\<Sum>i\<le>n. p i * i) = n"

theorem euler_partition_theorem:
  fixes n :: nat
  shows "card {p. nat_partition n p \<and> (\<forall>i. p i \<noteq> 0 \<longrightarrow> odd i)} =
    card {p. nat_partition n p \<and> (\<forall>i. p i \<le> 1)}"
  sorry

end
