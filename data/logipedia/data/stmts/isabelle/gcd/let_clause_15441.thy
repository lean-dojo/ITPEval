(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_15441, catalog title "gcd.let_clause_15441": under the stated
  natural-number bounds, nondivisibility, and coefficient hypotheses,
  commuting the factors in the minuend of the second truncated-difference
  equality preserves the fuel-indexed auxiliary gcd value. This file contains
  no proof.
*)

theory let_clause_15441
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

theorem let_clause_15441:
  "\<forall>p q :: nat.
    (\<forall>m n :: nat.
      0 < n \<longrightarrow>
      n \<le> m \<longrightarrow>
      n \<le> q \<longrightarrow>
      (\<exists>a b :: nat.
        a * n - b * m = gcd_aux q m n \<or>
        b * m - a * n = gcd_aux q m n)) \<longrightarrow>
    (\<forall>m n :: nat.
      0 < n \<longrightarrow>
      n \<le> m \<longrightarrow>
      n \<le> Suc q \<longrightarrow>
      \<not> n dvd m \<longrightarrow>
      (\<forall>a :: nat.
        (\<exists>b :: nat.
          a * logipedia_mod m n - b * n =
            gcd_aux q n (logipedia_mod m n) \<or>
          b * n - a * logipedia_mod m n =
            gcd_aux q n (logipedia_mod m n)) \<longrightarrow>
        (\<forall>b :: nat.
          (a * logipedia_mod m n - b * n =
             gcd_aux q n (logipedia_mod m n) \<or>
           b * n - a * logipedia_mod m n =
             gcd_aux q n (logipedia_mod m n)) \<longrightarrow>
          b * n - a * logipedia_mod m n =
            gcd_aux q n (logipedia_mod m n) \<longrightarrow>
          n * b - a * logipedia_mod m n =
            gcd_aux q n (logipedia_mod m n))))"
  sorry

end
