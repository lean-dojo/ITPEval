(*
  Statement-only formalization of Logipedia corpus artifact
  nat.sym_eq_minus_body_S, catalog title "nat.sym_eq_minus_body_S": for every
  natural number, the natural-number matcher that returns its successor at
  zero and delegates to subtraction at predecessors is Leibniz-equal to the
  abstract subtraction body at that successor. This file contains no proof.
*)

theory sym_eq_minus_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_minus_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (\<lambda>m :: nat.
        case m of 0 \<Rightarrow> Suc n | Suc q \<Rightarrow> minus n q)
      (minus_body (Suc n))"
  sorry

end
