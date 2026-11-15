(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q180345X, "Integral root theorem": a root in a fraction field of a monic
  polynomial over a unique factorization domain lies in the embedded base
  domain. This file contains no proof.
*)

theory Q180345X_integral_root_theorem
  imports Main
begin

definition q180345x_polynomial :: "(nat \<Rightarrow> 'a::zero) \<Rightarrow> bool" where
  "q180345x_polynomial c \<longleftrightarrow> finite {n. c n \<noteq> 0}"

definition q180345x_eval ::
    "('a::zero \<Rightarrow> 'k::comm_semiring_1) \<Rightarrow>
      (nat \<Rightarrow> 'a) \<Rightarrow> 'k \<Rightarrow> 'k" where
  "q180345x_eval incl c r =
    (\<Sum>n\<in>{n. c n \<noteq> 0}. incl (c n) * r ^ n)"

definition q180345x_lead_coeff :: "(nat \<Rightarrow> 'a::zero) \<Rightarrow> 'a" where
  "q180345x_lead_coeff c =
    (if {n. c n \<noteq> 0} = {} then 0 else c (Max {n. c n \<noteq> 0}))"

definition q180345x_unit :: "'a::comm_monoid_mult \<Rightarrow> bool" where
  "q180345x_unit u \<longleftrightarrow> (\<exists>v. u * v = 1)"

definition q180345x_irreducible ::
    "'a::{comm_monoid_mult,zero} \<Rightarrow> bool" where
  "q180345x_irreducible p \<longleftrightarrow>
    p \<noteq> 0 \<and> \<not> q180345x_unit p \<and>
    (\<forall>a b. p = a * b \<longrightarrow> q180345x_unit a \<or> q180345x_unit b)"

definition q180345x_prime :: "'a::{comm_monoid_mult,zero} \<Rightarrow> bool" where
  "q180345x_prime p \<longleftrightarrow>
    p \<noteq> 0 \<and> \<not> q180345x_unit p \<and>
    (\<forall>a b. p dvd a * b \<longrightarrow> p dvd a \<or> p dvd b)"

locale q180345x_fraction_field_ufd =
  fixes incl :: "'a::idom \<Rightarrow> 'k::field"
  assumes incl_zero: "incl 0 = 0"
    and incl_one: "incl 1 = 1"
    and incl_add: "\<And>x y. incl (x + y) = incl x + incl y"
    and incl_mult: "\<And>x y. incl (x * y) = incl x * incl y"
    and incl_inj: "\<And>x y. incl x = incl y \<Longrightarrow> x = y"
    and fraction_field:
      "\<And>r. \<exists>a b. b \<noteq> 0 \<and> r = incl a / incl b"
    and factorization:
      "\<And>x. x \<noteq> 0 \<Longrightarrow>
        \<exists>u ps. q180345x_unit u \<and>
          (\<forall>p\<in>set ps. q180345x_irreducible p) \<and>
          x = u * prod_list ps"
    and irreducible_prime:
      "\<And>p. q180345x_irreducible p \<Longrightarrow> q180345x_prime p"
begin

theorem isInteger_of_is_root_of_monic:
  fixes c :: "nat \<Rightarrow> 'a"
    and r :: 'k
  assumes "q180345x_polynomial c"
    and "q180345x_lead_coeff c = 1"
    and "q180345x_eval incl c r = 0"
  shows "\<exists>a. r = incl a"
  oops

end

end
