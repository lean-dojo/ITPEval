(*
  Statement-only formalization of Logipedia corpus artifact
  fermat.permut_mod, catalog title "fermat.permut_mod": multiplication by a
  natural number not divisible by a prime p, followed by reduction modulo p,
  permutes the naturals from 0 through p - 1. This file contains no proof.
*)

theory permut_mod
  imports Main
begin

definition logipedia_permut :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> bool"
  where
    "logipedia_permut f m \<longleftrightarrow>
      (\<forall>i. i \<le> m \<longrightarrow> f i \<le> m) \<and>
      (\<forall>i j. i \<le> m \<longrightarrow> j \<le> m \<longrightarrow>
        f i = f j \<longrightarrow> i = j)"

theorem permut_mod:
  fixes p a :: nat
  assumes "prime p"
    and "\<not> p dvd a"
  shows "logipedia_permut (\<lambda>n. (a * n) mod p) (p - 1)"
  sorry

end
