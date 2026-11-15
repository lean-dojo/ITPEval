(*
  Statement-only formalization of thousand-theorems corpus artifact Q3527205,
  canonical artifact thousand-theorems__isabelle__Q3527205, "Dimension theorem
  for vector spaces": over a semiring with invariant basis number, any two
  indexed bases of the same semimodule have equipotent index types. This file
  contains no proof.
*)

theory Q3527205_dimension_theorem_for_vector_spaces
  imports Main
begin

definition q3527205_module ::
    "('r::semiring_1 \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q3527205_module smult \<longleftrightarrow>
    (\<forall>a x y. smult a (x + y) = smult a x + smult a y) \<and>
    (\<forall>a b x. smult (a + b) x = smult a x + smult b x) \<and>
    (\<forall>x. smult 0 x = 0) \<and>
    (\<forall>a. smult a 0 = 0) \<and>
    (\<forall>a b x. smult (a * b) x = smult a (smult b x)) \<and>
    (\<forall>x. smult 1 x = x)"

definition q3527205_finitely_supported ::
    "('i \<Rightarrow> 'r::zero) set" where
  "q3527205_finitely_supported =
    {c. finite {i. c i \<noteq> 0}}"

definition q3527205_linear_combination ::
    "('r::semiring_1 \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm) \<Rightarrow>
      ('i \<Rightarrow> 'm) \<Rightarrow> ('i \<Rightarrow> 'r) \<Rightarrow> 'm" where
  "q3527205_linear_combination smult b c =
    (\<Sum>i\<in>{i. c i \<noteq> 0}. smult (c i) (b i))"

definition q3527205_basis ::
    "('r::semiring_1 \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm) \<Rightarrow>
      ('i \<Rightarrow> 'm) \<Rightarrow> bool" where
  "q3527205_basis smult b \<longleftrightarrow>
    bij_betw (q3527205_linear_combination smult b)
      q3527205_finitely_supported UNIV"

definition q3527205_free_vectors ::
    "nat \<Rightarrow> (nat \<Rightarrow> 'r::semiring_1) set" where
  "q3527205_free_vectors n =
    {x. \<forall>i. n \<le> i \<longrightarrow> x i = 0}"

definition q3527205_free_linear_equiv ::
    "nat \<Rightarrow> nat \<Rightarrow>
      ((nat \<Rightarrow> 'r::semiring_1) \<Rightarrow> (nat \<Rightarrow> 'r)) \<Rightarrow>
      bool" where
  "q3527205_free_linear_equiv n m f \<longleftrightarrow>
    bij_betw f (q3527205_free_vectors n) (q3527205_free_vectors m) \<and>
    (\<forall>x\<in>q3527205_free_vectors n.
      \<forall>y\<in>q3527205_free_vectors n.
        f (\<lambda>i. x i + y i) = (\<lambda>i. f x i + f y i)) \<and>
    (\<forall>a. \<forall>x\<in>q3527205_free_vectors n.
      f (\<lambda>i. a * x i) = (\<lambda>i. a * f x i))"

definition q3527205_invariant_basis_number ::
    "'r::semiring_1 itself \<Rightarrow> bool" where
  "q3527205_invariant_basis_number TYPE('r) \<longleftrightarrow>
    (\<forall>n m.
      (\<exists>f :: (nat \<Rightarrow> 'r) \<Rightarrow> (nat \<Rightarrow> 'r).
        q3527205_free_linear_equiv n m f) \<longrightarrow>
      n = m)"

theorem mk_eq_mk_of_basis:
  fixes smult :: "'r::semiring_1 \<Rightarrow> 'm::comm_monoid_add \<Rightarrow> 'm"
    and v :: "'i \<Rightarrow> 'm"
    and v' :: "'j \<Rightarrow> 'm"
  assumes module: "q3527205_module smult"
    and invariant_basis_number:
      "q3527205_invariant_basis_number TYPE('r)"
    and basis_v: "q3527205_basis smult v"
    and basis_v': "q3527205_basis smult v'"
  shows "ordIso2 (card_of (UNIV :: 'i set)) (card_of (UNIV :: 'j set))"
  sorry

end
