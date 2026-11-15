(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q1566341 (thousand-theorems__isabelle__Q1566341), "Hindman's theorem": in
  any finite cover of the finite-product set of an infinite sequence in a
  semigroup, one cell contains the finite-product set of another infinite
  sequence. This file contains no proof.
*)

theory Q1566341_hindman_s_theorem
  imports Main
begin

inductive q1566341_FP ::
    "(nat \<Rightarrow> 'a::semigroup_mult) \<Rightarrow> 'a \<Rightarrow> bool"
  where
    head: "q1566341_FP a (a 0)"
  | tail:
      "q1566341_FP (\<lambda>n. a (Suc n)) x \<Longrightarrow>
        q1566341_FP a x"
  | cons:
      "q1566341_FP (\<lambda>n. a (Suc n)) x \<Longrightarrow>
        q1566341_FP a (a 0 * x)"

theorem FP_partition_regular:
  fixes a :: "nat \<Rightarrow> 'a::semigroup_mult"
    and s :: "'a set set"
  assumes sfin: "finite s"
    and scov: "{x. q1566341_FP a x} \<subseteq> \<Union>s"
  shows "\<exists>c \<in> s. \<exists>b :: nat \<Rightarrow> 'a.
    {x. q1566341_FP b x} \<subseteq> c"
  sorry

end
