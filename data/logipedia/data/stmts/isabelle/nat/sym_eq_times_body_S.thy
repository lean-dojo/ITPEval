(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_times_body_S, catalog title "nat.sym_eq_times_body_S": for every
  natural number, the function mapping each natural number to its sum with the
  corresponding multiplication value is Leibniz-equal to the abstract
  multiplication body at the successor. This file contains no proof.
*)

theory sym_eq_times_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_times_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (\<lambda>m :: nat. plus m (times n m))
      (times_body (Suc n))"
  sorry

end
