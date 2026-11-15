(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.eq_minus_gcd_aux, catalog title "gcd.eq_minus_gcd_aux": for positive
  natural n bounded above by m and by the recursion index p, natural
  coefficients make one of the two truncated differences of multiples equal
  the recursively specified auxiliary gcd value. This file contains no proof.
*)

theory eq_minus_gcd_aux
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

definition logipedia_dividesb :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "logipedia_dividesb n m = (logipedia_mod m n = 0)"

fun gcd_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "gcd_aux 0 m n = m"
| "gcd_aux (Suc p) m n =
    (if logipedia_dividesb n m
     then n
     else gcd_aux p n (logipedia_mod m n))"

theorem eq_minus_gcd_aux:
  "\<forall>p m n :: nat.
    0 < n \<longrightarrow>
    n \<le> m \<longrightarrow>
    n \<le> p \<longrightarrow>
    (\<exists>a b :: nat.
      a * n - b * m = gcd_aux p m n \<or>
      b * m - a * n = gcd_aux p m n)"
  sorry

end
