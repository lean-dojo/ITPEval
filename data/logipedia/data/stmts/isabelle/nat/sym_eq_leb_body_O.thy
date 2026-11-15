(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_leb_body_O, catalog title "nat.sym_eq_leb_body_O": the
  constant-true function on natural numbers is Leibniz-equal to the abstract
  Boolean less-than-or-equal body at zero. This file contains no proof.
*)

theory sym_eq_leb_body_O
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<longleftrightarrow>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"

theorem sym_eq_leb_body_O:
  "logipedia_leibniz
    (\<lambda>m :: nat. True)
    (leb_body 0 :: nat \<Rightarrow> bool)"
  sorry

end
