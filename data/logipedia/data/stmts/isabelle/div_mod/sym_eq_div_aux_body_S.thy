(*
  Statement-only formalization of Logipedia corpus artifact
  div_mod.sym_eq_div_aux_body_S, catalog title
  "div_mod.sym_eq_div_aux_body_S": at a successor index, the curried
  natural-number function that returns zero when the dividend is at most the
  divisor and otherwise returns the successor of the recursive auxiliary
  quotient is Leibniz-equal to the abstract auxiliary division body. This
  file contains no proof.
*)

theory sym_eq_div_aux_body_S
  imports Main
begin

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  div_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  div_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_div_aux_body_S:
  "\<forall>p :: nat.
    logipedia_leibniz
      (\<lambda>m n.
        if m \<le> n
        then 0
        else Suc (div_aux p (m - Suc n) n))
      (div_aux_body (Suc p) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
