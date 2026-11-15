(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_plus_body_S, catalog title "nat.eq_plus_body_S": for every natural
  number, the abstract addition body at its successor is Leibniz-equal to the
  function mapping each natural number to the successor of its sum with the
  original number. This file contains no proof.
*)

theory eq_plus_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  plus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  plus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_plus_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (plus_body (Suc n))
      (\<lambda>m :: nat. Suc (plus n m))"
  sorry

end
