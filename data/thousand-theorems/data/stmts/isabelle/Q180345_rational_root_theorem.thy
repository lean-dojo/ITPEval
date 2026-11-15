(*
  Statement-only formalization of the thousand-theorems corpus artifact
  thousand-theorems__isabelle__Q180345, "Rational root theorem": for a
  polynomial over a unique factorization domain, the reduced numerator and
  denominator of a root in its fraction field divide the constant and leading
  coefficients, respectively. This file contains no proof.
*)

theory Q180345_rational_root_theorem
  imports Main
begin

definition q180345_polynomial :: "(nat \<Rightarrow> 'a::zero) \<Rightarrow> bool" where
  "q180345_polynomial c \<longleftrightarrow> finite {n. c n \<noteq> 0}"

definition q180345_eval ::
    "('a::zero \<Rightarrow> 'k::comm_semiring_1) \<Rightarrow>
      (nat \<Rightarrow> 'a) \<Rightarrow> 'k \<Rightarrow> 'k" where
  "q180345_eval incl c r =
    (\<Sum>n\<in>{n. c n \<noteq> 0}. incl (c n) * r ^ n)"

definition q180345_lead_coeff :: "(nat \<Rightarrow> 'a::zero) \<Rightarrow> 'a" where
  "q180345_lead_coeff c =
    (if {n. c n \<noteq> 0} = {} then 0 else c (Max {n. c n \<noteq> 0}))"

definition q180345_unit :: "'a::comm_monoid_mult \<Rightarrow> bool" where
  "q180345_unit u \<longleftrightarrow> (\<exists>v. u * v = 1)"

definition q180345_coprime :: "'a::comm_monoid_mult \<Rightarrow> 'a \<Rightarrow> bool" where
  "q180345_coprime a b \<longleftrightarrow>
    (\<forall>d. d dvd a \<longrightarrow> d dvd b \<longrightarrow> q180345_unit d)"

definition q180345_irreducible ::
    "'a::{comm_monoid_mult,zero} \<Rightarrow> bool" where
  "q180345_irreducible p \<longleftrightarrow>
    p \<noteq> 0 \<and> \<not> q180345_unit p \<and>
    (\<forall>a b. p = a * b \<longrightarrow> q180345_unit a \<or> q180345_unit b)"

definition q180345_prime :: "'a::{comm_monoid_mult,zero} \<Rightarrow> bool" where
  "q180345_prime p \<longleftrightarrow>
    p \<noteq> 0 \<and> \<not> q180345_unit p \<and>
    (\<forall>a b. p dvd a * b \<longrightarrow> p dvd a \<or> p dvd b)"

locale q180345_fraction_field_ufd =
  fixes incl :: "'a::idom \<Rightarrow> 'k::field"
    and num :: "'k \<Rightarrow> 'a"
    and den :: "'k \<Rightarrow> 'a"
  assumes incl_zero: "incl 0 = 0"
    and incl_one: "incl 1 = 1"
    and incl_add: "incl (x + y) = incl x + incl y"
    and incl_mult: "incl (x * y) = incl x * incl y"
    and incl_inj: "incl x = incl y \<Longrightarrow> x = y"
    and num_den_rep:
      "den r \<noteq> 0 \<and> r = incl (num r) / incl (den r)"
    and num_den_reduced: "q180345_coprime (num r) (den r)"
    and factorization:
      "x \<noteq> 0 \<Longrightarrow>
        \<exists>u ps. q180345_unit u \<and>
          (\<forall>p\<in>set ps. q180345_irreducible p) \<and>
          x = u * prod_list ps"
    and irreducible_prime:
      "q180345_irreducible p \<Longrightarrow> q180345_prime p"
begin

theorem num_dvd_of_is_root:
  fixes c :: "nat \<Rightarrow> 'a"
    and r :: 'k
  assumes "q180345_polynomial c"
    and "q180345_eval incl c r = 0"
  shows "num r dvd c 0"
  sorry

theorem den_dvd_of_is_root:
  fixes c :: "nat \<Rightarrow> 'a"
    and r :: 'k
  assumes "q180345_polynomial c"
    and "q180345_eval incl c r = 0"
  shows "den r dvd q180345_lead_coeff c"
  sorry

end

end
