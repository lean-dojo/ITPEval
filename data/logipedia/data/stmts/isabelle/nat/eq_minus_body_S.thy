(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_minus_body_S, catalog title "nat.eq_minus_body_S": for every natural
  number, the abstract subtraction body at its successor is Leibniz-equal to
  the natural-number matcher that returns the successor at zero and delegates
  to subtraction at the predecessor on successors. This file contains no
  proof.
*)

theory eq_minus_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  minus :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  minus_body :: "nat \<Rightarrow> nat \<Rightarrow> nat"

theorem eq_minus_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (minus_body (Suc n))
      (\<lambda>m :: nat.
        case m of 0 \<Rightarrow> Suc n | Suc q \<Rightarrow> minus n q)"
  sorry

end
