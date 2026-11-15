(*
  Statement-only formalization of thousand-theorems corpus artifact Q4695203
  (thousand-theorems__isabelle__Q4695203), "Four functions theorem":
  nonnegative functions on a distributive lattice satisfying a pointwise
  meet-join inequality satisfy the corresponding product-of-sums inequality
  for finite subsets. This file contains no proof.
*)

theory Q4695203_four_functions_theorem
  imports Main
begin

class q4695203_coefficient =
  linordered_comm_semiring_strict + comm_monoid_mult + zero_less_one +
  assumes q4695203_exists_add_of_le:
    "x \<le> y \<Longrightarrow> \<exists>z. y = x + z"

definition q4695203_pairwise_infs ::
    "'a::distrib_lattice set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "q4695203_pairwise_infs s t =
    {x. \<exists>a\<in>s. \<exists>b\<in>t. x = inf a b}"

definition q4695203_pairwise_sups ::
    "'a::distrib_lattice set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "q4695203_pairwise_sups s t =
    {x. \<exists>a\<in>s. \<exists>b\<in>t. x = sup a b}"

theorem four_functions_theorem:
  fixes f1 f2 f3 f4 :: "'a::distrib_lattice \<Rightarrow> 'b::q4695203_coefficient"
    and s t :: "'a set"
  assumes finite_s: "finite s"
    and finite_t: "finite t"
    and nonnegative_f1: "\<And>x. 0 \<le> f1 x"
    and nonnegative_f2: "\<And>x. 0 \<le> f2 x"
    and nonnegative_f3: "\<And>x. 0 \<le> f3 x"
    and nonnegative_f4: "\<And>x. 0 \<le> f4 x"
    and pointwise:
      "\<And>a b. f1 a * f2 b \<le> f3 (inf a b) * f4 (sup a b)"
  shows
    "(\<Sum>a\<in>s. f1 a) * (\<Sum>a\<in>t. f2 a) \<le>
      (\<Sum>a\<in>q4695203_pairwise_infs s t. f3 a) *
      (\<Sum>a\<in>q4695203_pairwise_sups s t. f4 a)"
  sorry

end
