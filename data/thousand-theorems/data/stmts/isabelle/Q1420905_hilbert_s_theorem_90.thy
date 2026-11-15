(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1420905 (thousand-theorems__isabelle__Q1420905), "Hilbert's theorem 90":
  for a finite cyclic Galois extension, every element of norm one is a
  quotient of a nonzero element by its image under a chosen generator of the
  Galois group. This file contains no proof.
*)

theory Q1420905_hilbert_s_theorem_90
  imports Main
begin

definition q1420905_field_embedding ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> bool" where
  "q1420905_field_embedding emb \<longleftrightarrow>
    inj emb \<and>
    emb 0 = 0 \<and>
    emb 1 = 1 \<and>
    (\<forall>a b. emb (a + b) = emb a + emb b) \<and>
    (\<forall>a b. emb (a * b) = emb a * emb b)"

definition q1420905_field_automorphism ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> ('l \<Rightarrow> 'l) \<Rightarrow> bool" where
  "q1420905_field_automorphism emb sigma \<longleftrightarrow>
    bij sigma \<and>
    sigma 0 = 0 \<and>
    sigma 1 = 1 \<and>
    (\<forall>x y. sigma (x + y) = sigma x + sigma y) \<and>
    (\<forall>x y. sigma (x * y) = sigma x * sigma y) \<and>
    (\<forall>a. sigma (emb a) = emb a)"

definition q1420905_galois_group ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> ('l \<Rightarrow> 'l) set" where
  "q1420905_galois_group emb =
    {sigma. q1420905_field_automorphism emb sigma}"

definition q1420905_linear_combination ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> 'l set \<Rightarrow>
      ('l \<Rightarrow> 'k) \<Rightarrow> 'l" where
  "q1420905_linear_combination emb B c =
    (\<Sum>b\<in>B. emb (c b) * b)"

definition q1420905_basis ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> 'l set \<Rightarrow> bool" where
  "q1420905_basis emb B \<longleftrightarrow>
    finite B \<and>
    (\<forall>c. q1420905_linear_combination emb B c = 0
      \<longrightarrow> (\<forall>b\<in>B. c b = 0)) \<and>
    (\<forall>x. \<exists>c. q1420905_linear_combination emb B c = x)"

definition q1420905_finite_galois_extension ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> bool" where
  "q1420905_finite_galois_extension emb \<longleftrightarrow>
    q1420905_field_embedding emb \<and>
    finite (q1420905_galois_group emb) \<and>
    (\<exists>B. q1420905_basis emb B \<and>
      card (q1420905_galois_group emb) = card B)"

definition q1420905_zpower ::
    "('a \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "q1420905_zpower f n =
    (if 0 \<le> n
      then f ^^ nat n
      else inv_into UNIV f ^^ nat (-n))"

definition q1420905_is_cyclic ::
    "('a \<Rightarrow> 'a) set \<Rightarrow> bool" where
  "q1420905_is_cyclic A \<longleftrightarrow>
    (\<exists>g\<in>A. \<forall>sigma\<in>A. \<exists>n::int. sigma = q1420905_zpower g n)"

definition q1420905_galois_norm ::
    "('k::field \<Rightarrow> 'l::field) \<Rightarrow> 'l \<Rightarrow> 'l" where
  "q1420905_galois_norm emb x =
    (\<Prod>sigma\<in>q1420905_galois_group emb. sigma x)"

theorem q1420905_hilbert_s_theorem_90:
  fixes emb :: "'k::field \<Rightarrow> 'l::field"
    and g :: "'l \<Rightarrow> 'l"
    and x :: "'l"
  assumes extension: "q1420905_finite_galois_extension emb"
    and cyclic: "q1420905_is_cyclic (q1420905_galois_group emb)"
    and generator:
      "g \<in> q1420905_galois_group emb \<and>
        (\<forall>sigma\<in>q1420905_galois_group emb.
          \<exists>n::int. sigma = q1420905_zpower g n)"
    and norm_one: "q1420905_galois_norm emb x = 1"
  shows "\<exists>y::'l. y \<noteq> 0 \<and> y / g y = x"
  sorry

end
