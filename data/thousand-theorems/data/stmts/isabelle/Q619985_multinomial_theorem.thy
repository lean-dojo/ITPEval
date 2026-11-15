(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q619985 (thousand-theorems__isabelle__Q619985), "Multinomial theorem":
  a natural power of a finite sum of pairwise-commuting elements of a semiring
  expands using multinomial coefficients and finite noncommutative products.
  This file contains no proof.
*)

theory Q619985_multinomial_theorem
  imports Main
begin

definition q619985_pi_antidiag :: "'i set \<Rightarrow> nat \<Rightarrow> ('i \<Rightarrow> nat) set" where
  "q619985_pi_antidiag s n =
    {k. (\<forall>i. i \<notin> s \<longrightarrow> k i = 0) \<and> (\<Sum>i\<in>s. k i) = n}"

definition q619985_multinomial :: "'i set \<Rightarrow> ('i \<Rightarrow> nat) \<Rightarrow> nat" where
  "q619985_multinomial s k =
    fact (\<Sum>i\<in>s. k i) div (\<Prod>i\<in>s. fact (k i))"

definition q619985_nat_cast :: "nat \<Rightarrow> 'a::{semiring_0,monoid_mult}" where
  "q619985_nat_cast n = (\<Sum>i<n. 1)"

definition q619985_index_list :: "'i set \<Rightarrow> 'i list" where
  "q619985_index_list s =
    (SOME xs. distinct xs \<and> set xs = s)"

definition q619985_noncomm_prod ::
    "'i set \<Rightarrow> ('i \<Rightarrow> 'a::monoid_mult) \<Rightarrow> 'a" where
  "q619985_noncomm_prod s g =
    foldr (\<lambda>i acc. g i * acc) (q619985_index_list s) 1"

theorem sum_pow_eq_sum_pi_antidiag_of_commute:
  fixes s :: "'i set"
    and f :: "'i \<Rightarrow> 'a::{semiring_0,monoid_mult}"
    and n :: nat
  assumes finite_s: "finite s"
    and commute:
      "\<And>i j. i \<in> s \<Longrightarrow> j \<in> s \<Longrightarrow> i \<noteq> j \<Longrightarrow>
        f i * f j = f j * f i"
  shows "(\<Sum>i\<in>s. f i) ^ n =
    (\<Sum>k\<in>q619985_pi_antidiag s n.
      q619985_nat_cast (q619985_multinomial s k) *
        q619985_noncomm_prod s (\<lambda>i. f i ^ k i))"
  sorry

end
