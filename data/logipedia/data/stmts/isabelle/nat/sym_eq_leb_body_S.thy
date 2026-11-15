(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_leb_body_S, catalog title "nat.sym_eq_leb_body_S": for every
  natural number, the natural-number matcher that is false at zero and
  delegates to the preceding Boolean less-than-or-equal function on successors
  is Leibniz-equal to the abstract less-than-or-equal body at the successor.
  This file contains no proof.
*)

theory sym_eq_leb_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  leb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"

theorem sym_eq_leb_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (\<lambda>m :: nat.
        case m of 0 \<Rightarrow> False | Suc q \<Rightarrow> leb n q)
      (leb_body (Suc n))"
  sorry

end
