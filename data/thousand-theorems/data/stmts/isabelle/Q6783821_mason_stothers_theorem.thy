(*
  Statement-only formalization of the thousand-theorems corpus artifact Q6783821
  (thousand-theorems__isabelle__Q6783821), "Mason–Stothers theorem": for three
  nonzero polynomials over an arbitrary field whose sum is zero, with the first
  two coprime, each degree plus one is at most the degree of the squarefree
  radical of their product, or all three formal derivatives vanish. This file
  represents polynomials by finitely supported coefficient functions and
  contains no proof.
*)

theory Q6783821_mason_stothers_theorem
  imports Main
begin

type_synonym 'a q6783821_poly = "nat \<Rightarrow> 'a"

definition q6783821_support ::
    "'a::zero q6783821_poly \<Rightarrow> nat set" where
  "q6783821_support p = {n. p n \<noteq> 0}"

definition q6783821_is_poly :: "'a::zero q6783821_poly \<Rightarrow> bool" where
  "q6783821_is_poly p \<longleftrightarrow> finite (q6783821_support p)"

definition q6783821_zero :: "'a::zero q6783821_poly" where
  "q6783821_zero = (\<lambda>_. 0)"

definition q6783821_one :: "'a::{zero,one} q6783821_poly" where
  "q6783821_one = (\<lambda>n. if n = 0 then 1 else 0)"

definition q6783821_add ::
    "'a::plus q6783821_poly \<Rightarrow>
      'a q6783821_poly \<Rightarrow> 'a q6783821_poly" where
  "q6783821_add p q = (\<lambda>n. p n + q n)"

definition q6783821_mul ::
    "'a::comm_semiring_1 q6783821_poly \<Rightarrow>
      'a q6783821_poly \<Rightarrow> 'a q6783821_poly" where
  "q6783821_mul p q = (\<lambda>n. \<Sum>i\<le>n. p i * q (n - i))"

definition q6783821_deriv ::
    "'a::comm_semiring_1 q6783821_poly \<Rightarrow> 'a q6783821_poly" where
  "q6783821_deriv p = (\<lambda>n. of_nat (Suc n) * p (Suc n))"

definition q6783821_degree :: "'a::zero q6783821_poly \<Rightarrow> nat" where
  "q6783821_degree p =
    (if q6783821_support p = {} then 0 else Max (q6783821_support p))"

definition q6783821_divides ::
    "'a::field q6783821_poly \<Rightarrow>
      'a q6783821_poly \<Rightarrow> bool" where
  "q6783821_divides p q \<longleftrightarrow>
    q6783821_is_poly p \<and>
    q6783821_is_poly q \<and>
    (\<exists>r. q6783821_is_poly r \<and> q = q6783821_mul p r)"

definition q6783821_unit :: "'a::field q6783821_poly \<Rightarrow> bool" where
  "q6783821_unit p \<longleftrightarrow>
    q6783821_divides p q6783821_one"

definition q6783821_irreducible ::
    "'a::field q6783821_poly \<Rightarrow> bool" where
  "q6783821_irreducible p \<longleftrightarrow>
    q6783821_is_poly p \<and>
    p \<noteq> q6783821_zero \<and>
    \<not> q6783821_unit p \<and>
    (\<forall>u v.
      q6783821_is_poly u \<longrightarrow>
      q6783821_is_poly v \<longrightarrow>
      p = q6783821_mul u v \<longrightarrow>
      q6783821_unit u \<or> q6783821_unit v)"

definition q6783821_monic :: "'a::field q6783821_poly \<Rightarrow> bool" where
  "q6783821_monic p \<longleftrightarrow>
    q6783821_is_poly p \<and>
    p \<noteq> q6783821_zero \<and>
    p (q6783821_degree p) = 1"

definition q6783821_coprime ::
    "'a::field q6783821_poly \<Rightarrow>
      'a q6783821_poly \<Rightarrow> bool" where
  "q6783821_coprime a b \<longleftrightarrow>
    q6783821_is_poly a \<and>
    q6783821_is_poly b \<and>
    (\<exists>x y.
      q6783821_is_poly x \<and>
      q6783821_is_poly y \<and>
      q6783821_add (q6783821_mul x a) (q6783821_mul y b) =
        q6783821_one)"

definition q6783821_radical_degree ::
    "'a::field q6783821_poly \<Rightarrow> nat" where
  "q6783821_radical_degree p =
    (\<Sum>q\<in>{q.
      q6783821_irreducible q \<and>
      q6783821_monic q \<and>
      q6783821_divides q p}.
      q6783821_degree q)"

theorem q6783821_mason_stothers:
  fixes a b c :: "'a::field q6783821_poly"
  assumes "q6783821_is_poly a"
    and "q6783821_is_poly b"
    and "q6783821_is_poly c"
    and "a \<noteq> q6783821_zero"
    and "b \<noteq> q6783821_zero"
    and "c \<noteq> q6783821_zero"
    and "q6783821_coprime a b"
    and "q6783821_add (q6783821_add a b) c = q6783821_zero"
  shows
    "(q6783821_degree a + 1 \<le>
        q6783821_radical_degree (q6783821_mul (q6783821_mul a b) c) \<and>
      q6783821_degree b + 1 \<le>
        q6783821_radical_degree (q6783821_mul (q6783821_mul a b) c) \<and>
      q6783821_degree c + 1 \<le>
        q6783821_radical_degree (q6783821_mul (q6783821_mul a b) c)) \<or>
      (q6783821_deriv a = q6783821_zero \<and>
        q6783821_deriv b = q6783821_zero \<and>
        q6783821_deriv c = q6783821_zero)"
  sorry

end
