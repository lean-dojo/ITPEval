(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_times_body_O, catalog title "nat.sym_eq_times_body_O": the
  constant-zero function on natural numbers is Leibniz-equal to the abstract
  natural-number multiplication body at zero. This file contains no proof.
*)

theory sym_eq_times_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts times_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_times_body_O:
  "logipedia_leibniz
    (\<lambda>m :: nat. 0)
    (times_body 0)"
  sorry

end
