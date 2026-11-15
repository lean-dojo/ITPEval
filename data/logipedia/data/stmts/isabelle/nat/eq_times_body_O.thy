(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_times_body_O, catalog title "nat.eq_times_body_O": the abstract
  natural-number multiplication body at zero is Leibniz-equal to the
  constant-zero function. This file contains no proof.
*)

theory eq_times_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_times_body_O:
  "logipedia_leibniz
    (times_body 0)
    (\<lambda>m :: nat. 0)"
  sorry

end
