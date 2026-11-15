(*
  Statement-only formalization of the thousand-theorems corpus artifact Q2253746,
  "Bertrand's ballot theorem": among vote lists with p entries equal to 1 and q
  entries equal to -1, where q < p, the uniform probability that every nonempty
  suffix has positive sum is (p - q) / (p + q). This file contains no proof.
*)

theory Q2253746_bertrand_s_ballot_theorem
  imports Complex_Main
begin

definition q2253746_stays_positive :: "int list set" where
  "q2253746_stays_positive =
    {xs. \<forall>ys. ys \<noteq> [] \<longrightarrow>
      (\<exists>zs. xs = zs @ ys) \<longrightarrow> 0 < sum_list ys}"

definition q2253746_counted_sequence :: "nat \<Rightarrow> nat \<Rightarrow> int list set" where
  "q2253746_counted_sequence p q =
    {xs. count_list xs 1 = p \<and>
      count_list xs (-1) = q \<and>
      (\<forall>x \<in> set xs. x = 1 \<or> x = -1)}"

definition q2253746_uniform_probability :: "'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "q2253746_uniform_probability S A =
    real (card (S \<inter> A)) / real (card S)"

theorem ballot_problem:
  fixes q p :: nat
  assumes "q < p"
  shows
    "q2253746_uniform_probability
      (q2253746_counted_sequence p q) q2253746_stays_positive =
      real (p - q) / real (p + q)"
  sorry

end
