(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.sym_eq_gcd_aux_body_S, catalog title "gcd.sym_eq_gcd_aux_body_S": for
  every natural recursion index, the curried gcd step function selected by
  the source divisibility test is Leibniz-equal to the abstract auxiliary gcd
  body at the successor index. This file contains no proof.
*)

theory sym_eq_gcd_aux_body_S
  imports Main
begin

primrec logipedia_mod_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_mod_aux 0 n m = n"
| "logipedia_mod_aux (Suc p) n m =
    (if n \<le> m then n else logipedia_mod_aux p (n - Suc m) m)"

definition logipedia_mod :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "logipedia_mod n m =
    (case m of
      0 \<Rightarrow> n
    | Suc p \<Rightarrow> logipedia_mod_aux n n p)"

definition logipedia_match_bool_type :: "'a \<Rightarrow> 'a \<Rightarrow> bool \<Rightarrow> 'a"
where
  "logipedia_match_bool_type case_true case_false b =
    (if b then case_true else case_false)"

definition logipedia_dividesb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_dividesb n m = (logipedia_mod m n = 0)"

definition logipedia_leibniz :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "logipedia_leibniz x y \<equiv>
    (\<forall>P :: 'a \<Rightarrow> bool. P x \<longrightarrow> P y)"

consts
  gcd_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  gcd_aux_body :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"

theorem sym_eq_gcd_aux_body_S:
  "\<forall>p :: nat.
    logipedia_leibniz
      (\<lambda>m :: nat. \<lambda>n :: nat.
        logipedia_match_bool_type
          n
          (gcd_aux p n (logipedia_mod m n))
          (logipedia_dividesb n m))
      (gcd_aux_body (Suc p) :: nat \<Rightarrow> nat \<Rightarrow> nat)"
  sorry

end
