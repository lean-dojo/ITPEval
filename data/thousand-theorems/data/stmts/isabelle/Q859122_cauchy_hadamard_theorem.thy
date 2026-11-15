(*
  Statement-only formalization of the thousand-theorems corpus artifact
  Q859122 (thousand-theorems__isabelle__Q859122),
  "Cauchy–Hadamard theorem": for a formal multilinear series over an arbitrary
  nontrivially normed field, the inverse of its convergence radius is the
  limsup of the nth roots of its coefficient operator norms. This file
  contains no proof.
*)

theory Q859122_cauchy_hadamard_theorem
  imports "HOL-Library.Extended_Nonnegative_Real"
begin

definition q859122_nontrivially_normed_field ::
    "('k::field \<Rightarrow> real) \<Rightarrow> bool" where
  "q859122_nontrivially_normed_field knorm \<longleftrightarrow>
    knorm 0 = 0 \<and>
    (\<forall>a. 0 \<le> knorm a) \<and>
    (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
    (\<forall>a. knorm (-a) = knorm a) \<and>
    (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
    (\<forall>a b. knorm (a * b) = knorm a * knorm b) \<and>
    (\<exists>a. 1 < knorm a)"

definition q859122_normed_space ::
    "('k::field \<Rightarrow> real) \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow> bool" where
  "q859122_normed_space knorm enorm scale \<longleftrightarrow>
    enorm 0 = 0 \<and>
    (\<forall>x. 0 \<le> enorm x) \<and>
    (\<forall>x. enorm x = 0 \<longleftrightarrow> x = 0) \<and>
    (\<forall>x. enorm (-x) = enorm x) \<and>
    (\<forall>x y. enorm (x + y) \<le> enorm x + enorm y) \<and>
    (\<forall>a x y. scale a (x + y) = scale a x + scale a y) \<and>
    (\<forall>a b x. scale (a + b) x = scale a x + scale b x) \<and>
    (\<forall>a b x. scale (a * b) x = scale a (scale b x)) \<and>
    (\<forall>x. scale 1 x = x) \<and>
    (\<forall>a x. enorm (scale a x) = knorm a * enorm x)"

definition q859122_continuous_multilinear ::
    "nat \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('k::field \<Rightarrow> 'e \<Rightarrow> 'e) \<Rightarrow>
      ('k \<Rightarrow> 'f \<Rightarrow> 'f) \<Rightarrow>
      ('e list \<Rightarrow> 'f) \<Rightarrow> bool" where
  "q859122_continuous_multilinear n enorm fnorm escale fscale A
      \<longleftrightarrow>
    (\<forall>xs i u v.
      length xs = n \<longrightarrow> i < n \<longrightarrow>
      A (xs[i := u + v]) = A (xs[i := u]) + A (xs[i := v])) \<and>
    (\<forall>xs i a u.
      length xs = n \<longrightarrow> i < n \<longrightarrow>
      A (xs[i := escale a u]) = fscale a (A (xs[i := u]))) \<and>
    (\<exists>C\<ge>0. \<forall>xs. length xs = n \<longrightarrow>
      fnorm (A xs) \<le> C * (\<Prod>i<n. enorm (xs ! i)))"

definition q859122_multilinear_operator_norm ::
    "nat \<Rightarrow>
      ('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('e list \<Rightarrow> 'f) \<Rightarrow> real" where
  "q859122_multilinear_operator_norm n enorm fnorm A =
    Inf {C. 0 \<le> C \<and> (\<forall>xs. length xs = n \<longrightarrow>
      fnorm (A xs) \<le> C * (\<Prod>i<n. enorm (xs ! i)))}"

definition q859122_radius ::
    "('e::ab_group_add \<Rightarrow> real) \<Rightarrow>
      ('f::ab_group_add \<Rightarrow> real) \<Rightarrow>
      (nat \<Rightarrow> 'e list \<Rightarrow> 'f) \<Rightarrow> ennreal" where
  "q859122_radius enorm fnorm A =
    Sup ((\<lambda>r::real. ennreal r) `
      {r. 0 \<le> r \<and> (\<exists>C::real. \<forall>n.
        q859122_multilinear_operator_norm n enorm fnorm (A n) * r ^ n
          \<le> C)})"

definition q859122_root_coefficient :: "real \<Rightarrow> nat \<Rightarrow> ennreal" where
  "q859122_root_coefficient x n =
    ennreal (if n = 0 then 1 else x powr (1 / real n))"

theorem q859122_cauchy_hadamard:
  fixes knorm :: "'k::field \<Rightarrow> real"
    and enorm :: "'e::ab_group_add \<Rightarrow> real"
    and fnorm :: "'f::ab_group_add \<Rightarrow> real"
    and escale :: "'k \<Rightarrow> 'e \<Rightarrow> 'e"
    and fscale :: "'k \<Rightarrow> 'f \<Rightarrow> 'f"
    and A :: "nat \<Rightarrow> 'e list \<Rightarrow> 'f"
  assumes scalar_field: "q859122_nontrivially_normed_field knorm"
    and domain_space: "q859122_normed_space knorm enorm escale"
    and codomain_space: "q859122_normed_space knorm fnorm fscale"
    and formal_multilinear_series:
      "\<forall>n. q859122_continuous_multilinear
        n enorm fnorm escale fscale (A n)"
  shows
    "inverse (q859122_radius enorm fnorm A) =
      limsup (\<lambda>n.
        q859122_root_coefficient
          (q859122_multilinear_operator_norm n enorm fnorm (A n)) n)"
  sorry

end
