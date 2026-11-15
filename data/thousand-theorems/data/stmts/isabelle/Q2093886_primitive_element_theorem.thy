(*
  Statement-only formalization of the thousand-theorems corpus artifact Q2093886,
  (thousand-theorems__isabelle__Q2093886), "Primitive element theorem": every
  finite-dimensional separable field extension is generated over its base field by
  a single element. This file contains no proof.
*)

theory Q2093886_primitive_element_theorem
  imports Main
begin

type_synonym 'a q2093886_poly = "nat \<Rightarrow> 'a"

definition q2093886_is_field_embedding ::
    "('f::field \<Rightarrow> 'e::field) \<Rightarrow> bool" where
  "q2093886_is_field_embedding emb \<longleftrightarrow>
    emb 0 = 0 \<and>
    emb 1 = 1 \<and>
    (\<forall>a b. emb (a + b) = emb a + emb b) \<and>
    (\<forall>a b. emb (a * b) = emb a * emb b)"

definition q2093886_poly_support ::
    "'a::zero q2093886_poly \<Rightarrow> nat set" where
  "q2093886_poly_support p = {n. p n \<noteq> 0}"

definition q2093886_is_poly ::
    "'a::zero q2093886_poly \<Rightarrow> bool" where
  "q2093886_is_poly p \<longleftrightarrow> finite (q2093886_poly_support p)"

definition q2093886_poly_zero ::
    "'a::zero q2093886_poly" where
  "q2093886_poly_zero = (\<lambda>_. 0)"

definition q2093886_poly_one ::
    "'a::zero_neq_one q2093886_poly" where
  "q2093886_poly_one = (\<lambda>n. if n = 0 then 1 else 0)"

definition q2093886_poly_add ::
    "'a::plus q2093886_poly \<Rightarrow>
      'a q2093886_poly \<Rightarrow> 'a q2093886_poly" where
  "q2093886_poly_add p q = (\<lambda>n. p n + q n)"

definition q2093886_poly_mul ::
    "'a::comm_semiring_1 q2093886_poly \<Rightarrow>
      'a q2093886_poly \<Rightarrow> 'a q2093886_poly" where
  "q2093886_poly_mul p q =
    (\<lambda>n. \<Sum>i\<le>n. p i * q (n - i))"

definition q2093886_poly_deriv ::
    "'a::comm_semiring_1 q2093886_poly \<Rightarrow> 'a q2093886_poly" where
  "q2093886_poly_deriv p =
    (\<lambda>n. of_nat (Suc n) * p (Suc n))"

definition q2093886_poly_eval ::
    "('f::field \<Rightarrow> 'e::field) \<Rightarrow>
      'f q2093886_poly \<Rightarrow> 'e \<Rightarrow> 'e" where
  "q2093886_poly_eval emb p x =
    (\<Sum>n\<in>q2093886_poly_support p. emb (p n) * x ^ n)"

definition q2093886_poly_coprime ::
    "'f::field q2093886_poly \<Rightarrow>
      'f q2093886_poly \<Rightarrow> bool" where
  "q2093886_poly_coprime p q \<longleftrightarrow>
    q2093886_is_poly p \<and>
    q2093886_is_poly q \<and>
    (\<exists>a b.
      q2093886_is_poly a \<and>
      q2093886_is_poly b \<and>
      q2093886_poly_add
        (q2093886_poly_mul a p)
        (q2093886_poly_mul b q) = q2093886_poly_one)"

definition q2093886_separable_extension ::
    "('f::field \<Rightarrow> 'e::field) \<Rightarrow> bool" where
  "q2093886_separable_extension emb \<longleftrightarrow>
    (\<forall>x. \<exists>p :: 'f q2093886_poly.
      q2093886_is_poly p \<and>
      p \<noteq> q2093886_poly_zero \<and>
      q2093886_poly_eval emb p x = 0 \<and>
      q2093886_poly_coprime p (q2093886_poly_deriv p))"

definition q2093886_finite_dimensional ::
    "('f::field \<Rightarrow> 'e::field) \<Rightarrow> bool" where
  "q2093886_finite_dimensional emb \<longleftrightarrow>
    (\<exists>B :: 'e set.
      finite B \<and>
      (\<forall>x. \<exists>c :: 'e \<Rightarrow> 'f.
        x = (\<Sum>b\<in>B. emb (c b) * b)))"

definition q2093886_intermediate_field ::
    "('f::field \<Rightarrow> 'e::field) \<Rightarrow> 'e set \<Rightarrow> bool" where
  "q2093886_intermediate_field emb K \<longleftrightarrow>
    (\<forall>a. emb a \<in> K) \<and>
    (\<forall>x\<in>K. \<forall>y\<in>K. x + y \<in> K) \<and>
    (\<forall>x\<in>K. -x \<in> K) \<and>
    (\<forall>x\<in>K. \<forall>y\<in>K. x * y \<in> K) \<and>
    (\<forall>x\<in>K. inverse x \<in> K)"

definition q2093886_adjoin_simple ::
    "('f::field \<Rightarrow> 'e::field) \<Rightarrow> 'e \<Rightarrow> 'e set" where
  "q2093886_adjoin_simple emb alpha =
    \<Inter>{K. q2093886_intermediate_field emb K \<and> alpha \<in> K}"

theorem q2093886_primitive_element_theorem:
  fixes emb :: "'f::field \<Rightarrow> 'e::field"
  assumes "q2093886_is_field_embedding emb"
    and "q2093886_finite_dimensional emb"
    and "q2093886_separable_extension emb"
  shows "\<exists>alpha :: 'e.
    q2093886_adjoin_simple emb alpha = UNIV"
  sorry

end
