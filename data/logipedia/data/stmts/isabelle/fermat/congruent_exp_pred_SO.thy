(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.congruent_exp_pred_SO, catalog title fermat.congruent_exp_pred_SO:
  Fermat's little theorem for natural numbers, stated as congruence of
  a^(p - 1) to 1 modulo a prime p that does not divide a. This file contains
  no proof.
*)

theory congruent_exp_pred_SO
  imports Main
begin

definition logipedia_divides :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_divides n m \<longleftrightarrow> (\<exists>q :: nat. m = n * q)"

definition logipedia_prime :: "nat \<Rightarrow> bool"
where
  "logipedia_prime p \<longleftrightarrow>
    1 < p \<and>
    (\<forall>m :: nat. logipedia_divides m p \<longrightarrow> 1 < m \<longrightarrow> m = p)"

definition congruent :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "congruent n m p \<longleftrightarrow> n mod p = m mod p"

theorem congruent_exp_pred_SO:
  fixes p a :: nat
  assumes "logipedia_prime p"
    and "\<not> logipedia_divides p a"
  shows "congruent (a ^ (p - 1)) 1 p"
  sorry

end
