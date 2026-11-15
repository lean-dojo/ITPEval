(*
  Statement-only formalization of Logipedia corpus artifact
  nat.eq_leb_body_S, catalog title "nat.eq_leb_body_S": for every natural
  number, the abstract Boolean less-than-or-equal body at its successor is
  Leibniz-equal to the natural-number matcher that is false at zero and
  delegates to the preceding less-than-or-equal function on successors. This
  file contains no proof.
*)

theory eq_leb_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  leb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  leb_body :: "nat \<Rightarrow> nat \<Rightarrow> bool"

theorem eq_leb_body_S:
  "\<forall>n :: nat.
    logipedia_leibniz
      (leb_body (Suc n))
      (\<lambda>m :: nat.
        case m of 0 \<Rightarrow> False | Suc q \<Rightarrow> leb n q)"
  sorry

end
