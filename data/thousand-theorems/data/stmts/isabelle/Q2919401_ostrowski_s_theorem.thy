(*
  Statement-only formalization of thousand-theorems corpus artifact Q2919401
  (thousand-theorems__isabelle__Q2919401), "Ostrowski's theorem": every
  nontrivial real-valued absolute value on the rational numbers is equivalent
  either to the usual absolute value or to the p-adic absolute value for a
  unique prime p. This file contains no proof.
*)

theory Q2919401_ostrowski_s_theorem
  imports Complex_Main
begin

definition q2919401_prime :: "nat \<Rightarrow> bool" where
  "q2919401_prime p \<longleftrightarrow>
    2 \<le> p \<and> (\<forall>d::nat. d dvd p \<longrightarrow> d = 1 \<or> d = p)"

definition q2919401_is_absolute_value :: "(rat \<Rightarrow> real) \<Rightarrow> bool" where
  "q2919401_is_absolute_value f \<longleftrightarrow>
    (\<forall>x y. f (x * y) = f x * f y) \<and>
    (\<forall>x. 0 \<le> f x) \<and>
    (\<forall>x. f x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x y. f (x + y) \<le> f x + f y)"

definition q2919401_is_nontrivial :: "(rat \<Rightarrow> real) \<Rightarrow> bool" where
  "q2919401_is_nontrivial f \<longleftrightarrow>
    (\<exists>x::rat. x \<noteq> 0 \<and> f x \<noteq> 1)"

definition q2919401_is_equiv ::
    "(rat \<Rightarrow> real) \<Rightarrow> (rat \<Rightarrow> real) \<Rightarrow> bool" where
  "q2919401_is_equiv f g \<longleftrightarrow>
    (\<forall>x y::rat. f x \<le> f y \<longleftrightarrow> g x \<le> g y)"

definition q2919401_real_absolute_value :: "rat \<Rightarrow> real" where
  "q2919401_real_absolute_value x = \<bar>of_rat x\<bar>"

definition q2919401_multiplicity :: "int \<Rightarrow> int \<Rightarrow> nat" where
  "q2919401_multiplicity p a =
    (if finite {n. p ^ n dvd a} then Max {n. p ^ n dvd a} else 0)"

definition q2919401_padic_absolute_value :: "nat \<Rightarrow> rat \<Rightarrow> real" where
  "q2919401_padic_absolute_value p x =
    (if x = 0 then 0 else
      let a = fst (quotient_of x);
          b = snd (quotient_of x)
      in real p powi
        (int (q2919401_multiplicity (int p) b) -
          int (q2919401_multiplicity (int p) a)))"

theorem ostrowski_s_theorem:
  fixes f :: "rat \<Rightarrow> real"
  assumes "q2919401_is_absolute_value f"
    and "q2919401_is_nontrivial f"
  shows
    "q2919401_is_equiv f q2919401_real_absolute_value \<or>
      (\<exists>!p::nat. q2919401_prime p \<and>
        q2919401_is_equiv f (q2919401_padic_absolute_value p))"
  sorry

end
