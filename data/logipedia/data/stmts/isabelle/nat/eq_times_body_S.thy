(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_times_body_S, catalog title "nat.eq_times_body_S": for every natural
  number, the abstract multiplication body at its successor is Leibniz-equal
  to the function mapping each natural number to its sum with the preceding
  multiplication value. This file contains no proof.
*)

theory eq_times_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_times_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (times_body (Suc n))
      (\<lambda>m :: nat. plus m (times n m))"
  sorry

end
