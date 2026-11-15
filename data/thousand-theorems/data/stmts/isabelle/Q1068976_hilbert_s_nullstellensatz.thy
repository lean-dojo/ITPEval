(*
  Statement-only formalization of thousand-theorems corpus artifact Q1068976,
  "Hilbert's Nullstellensatz": over an algebraically closed field extension,
  the ideal of finite-variable polynomials vanishing on an ideal's common zero
  locus is exactly the radical of that ideal. This file contains no proof.
*)

theory Q1068976_hilbert_s_nullstellensatz
  imports Main
begin

type_synonym ('v, 'a) raw_mpoly = "('v \<Rightarrow> nat) \<Rightarrow> 'a"

definition is_field_embedding ::
    "('k::field \<Rightarrow> 'K::field) \<Rightarrow> bool" where
  "is_field_embedding e \<longleftrightarrow>
    e 1 = 1 \<and>
    (\<forall>a b. e (a + b) = e a + e b) \<and>
    (\<forall>a b. e (a * b) = e a * e b)"

definition is_algebraically_closed ::
    "'K::field itself \<Rightarrow> bool" where
  "is_algebraically_closed _ \<longleftrightarrow>
    (\<forall>c :: nat \<Rightarrow> 'K.
      finite {n. c n \<noteq> 0} \<longrightarrow>
      (\<exists>n>0. c n \<noteq> 0) \<longrightarrow>
      (\<exists>x. (\<Sum>n\<in>{n. c n \<noteq> 0}. c n * x ^ n) = 0))"

definition monomial_support :: "('v \<Rightarrow> nat) \<Rightarrow> 'v set" where
  "monomial_support m = {v. m v \<noteq> 0}"

definition polynomial_support ::
    "('v, 'a::zero) raw_mpoly \<Rightarrow> ('v \<Rightarrow> nat) set" where
  "polynomial_support p = {m. p m \<noteq> 0}"

definition is_mpoly ::
    "('v, 'a::zero) raw_mpoly \<Rightarrow> bool" where
  "is_mpoly p \<longleftrightarrow>
    finite (polynomial_support p) \<and>
    (\<forall>m\<in>polynomial_support p. finite (monomial_support m))"

definition mpoly_zero :: "('v, 'a::zero) raw_mpoly" where
  "mpoly_zero = (\<lambda>_. 0)"

definition mpoly_one :: "('v, 'a::zero_neq_one) raw_mpoly" where
  "mpoly_one = (\<lambda>m. if m = (\<lambda>_. 0) then 1 else 0)"

definition mpoly_add ::
    "('v, 'a::plus) raw_mpoly \<Rightarrow>
      ('v, 'a) raw_mpoly \<Rightarrow> ('v, 'a) raw_mpoly" where
  "mpoly_add p q = (\<lambda>m. p m + q m)"

definition mpoly_neg ::
    "('v, 'a::uminus) raw_mpoly \<Rightarrow> ('v, 'a) raw_mpoly" where
  "mpoly_neg p = (\<lambda>m. - p m)"

definition mpoly_mul ::
    "('v, 'a::comm_semiring_1) raw_mpoly \<Rightarrow>
      ('v, 'a) raw_mpoly \<Rightarrow> ('v, 'a) raw_mpoly" where
  "mpoly_mul p q =
    (\<lambda>m.
      \<Sum>ab\<in>polynomial_support p \<times> polynomial_support q.
        if m = (\<lambda>v. fst ab v + snd ab v)
        then p (fst ab) * q (snd ab)
        else 0)"

fun mpoly_pow ::
    "('v, 'a::comm_semiring_1) raw_mpoly \<Rightarrow>
      nat \<Rightarrow> ('v, 'a) raw_mpoly" where
  "mpoly_pow p 0 = mpoly_one"
| "mpoly_pow p (Suc n) = mpoly_mul p (mpoly_pow p n)"

definition mpoly_eval ::
    "('k::zero \<Rightarrow> 'K::comm_semiring_1) \<Rightarrow>
      ('v \<Rightarrow> 'K) \<Rightarrow> ('v, 'k) raw_mpoly \<Rightarrow> 'K" where
  "mpoly_eval e x p =
    (\<Sum>m\<in>polynomial_support p.
      e (p m) * (\<Prod>v\<in>monomial_support m. x v ^ m v))"

definition is_ideal ::
    "('v, 'k::comm_ring_1) raw_mpoly set \<Rightarrow> bool" where
  "is_ideal I \<longleftrightarrow>
    (\<forall>p\<in>I. is_mpoly p) \<and>
    mpoly_zero \<in> I \<and>
    (\<forall>p\<in>I. \<forall>q\<in>I. mpoly_add p q \<in> I) \<and>
    (\<forall>p\<in>I. mpoly_neg p \<in> I) \<and>
    (\<forall>a. is_mpoly a \<longrightarrow>
      (\<forall>p\<in>I. mpoly_mul a p \<in> I))"

definition zero_locus ::
    "('k::zero \<Rightarrow> 'K::comm_semiring_1) \<Rightarrow>
      ('v, 'k) raw_mpoly set \<Rightarrow> ('v \<Rightarrow> 'K) set" where
  "zero_locus e I =
    {x. \<forall>p\<in>I. mpoly_eval e x p = 0}"

definition vanishing_ideal ::
    "('k::zero \<Rightarrow> 'K::comm_semiring_1) \<Rightarrow>
      ('v \<Rightarrow> 'K) set \<Rightarrow> ('v, 'k) raw_mpoly set" where
  "vanishing_ideal e V =
    {p. is_mpoly p \<and> (\<forall>x\<in>V. mpoly_eval e x p = 0)}"

definition ideal_radical ::
    "('v, 'k::comm_ring_1) raw_mpoly set \<Rightarrow>
      ('v, 'k) raw_mpoly set" where
  "ideal_radical I =
    {p. is_mpoly p \<and> (\<exists>n>0. mpoly_pow p n \<in> I)}"

theorem hilbert_nullstellensatz:
  fixes e :: "'k::field \<Rightarrow> 'K::field"
    and I :: "('v, 'k) raw_mpoly set"
  assumes "is_field_embedding e"
    and "is_algebraically_closed (TYPE('K))"
    and "finite (UNIV :: 'v set)"
    and "is_ideal I"
  shows "vanishing_ideal e (zero_locus e I) = ideal_radical I"
  sorry

end
