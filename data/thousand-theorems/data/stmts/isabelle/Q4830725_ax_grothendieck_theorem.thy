(*
  Statement-only formalization of thousand-theorems corpus artifact Q4830725
  (thousand-theorems__isabelle__Q4830725), "Ax-Grothendieck theorem": over an
  algebraically closed field with a finite coordinate carrier, an injective
  polynomial self-map of an ideal's zero locus is surjective on that locus.
  This file contains no proof.
*)

theory Q4830725_ax_grothendieck_theorem
  imports Main
begin

type_synonym ('v, 'a) q4830725_raw_mpoly = "('v \<Rightarrow> nat) \<Rightarrow> 'a"

definition q4830725_monomial_support ::
    "('v \<Rightarrow> nat) \<Rightarrow> 'v set" where
  "q4830725_monomial_support m = {v. m v \<noteq> 0}"

definition q4830725_polynomial_support ::
    "('v, 'a::zero) q4830725_raw_mpoly \<Rightarrow> ('v \<Rightarrow> nat) set" where
  "q4830725_polynomial_support p = {m. p m \<noteq> 0}"

definition q4830725_is_mpoly_on ::
    "'v set \<Rightarrow> ('v, 'a::zero) q4830725_raw_mpoly \<Rightarrow> bool" where
  "q4830725_is_mpoly_on V p \<longleftrightarrow>
    finite (q4830725_polynomial_support p) \<and>
    (\<forall>m\<in>q4830725_polynomial_support p.
      finite (q4830725_monomial_support m) \<and>
      q4830725_monomial_support m \<subseteq> V)"

definition q4830725_mpoly_zero ::
    "('v, 'a::zero) q4830725_raw_mpoly" where
  "q4830725_mpoly_zero = (\<lambda>_. 0)"

definition q4830725_mpoly_add ::
    "('v, 'a::plus) q4830725_raw_mpoly \<Rightarrow>
      ('v, 'a) q4830725_raw_mpoly \<Rightarrow>
      ('v, 'a) q4830725_raw_mpoly" where
  "q4830725_mpoly_add p q = (\<lambda>m. p m + q m)"

definition q4830725_mpoly_neg ::
    "('v, 'a::uminus) q4830725_raw_mpoly \<Rightarrow>
      ('v, 'a) q4830725_raw_mpoly" where
  "q4830725_mpoly_neg p = (\<lambda>m. - p m)"

definition q4830725_mpoly_mul ::
    "('v, 'a::comm_semiring_1) q4830725_raw_mpoly \<Rightarrow>
      ('v, 'a) q4830725_raw_mpoly \<Rightarrow>
      ('v, 'a) q4830725_raw_mpoly" where
  "q4830725_mpoly_mul p q =
    (\<lambda>m.
      \<Sum>ab\<in>q4830725_polynomial_support p
          \<times> q4830725_polynomial_support q.
        if m = (\<lambda>v. fst ab v + snd ab v)
        then p (fst ab) * q (snd ab)
        else 0)"

definition q4830725_mpoly_eval ::
    "('v \<Rightarrow> 'a::comm_semiring_1) \<Rightarrow>
      ('v, 'a) q4830725_raw_mpoly \<Rightarrow> 'a" where
  "q4830725_mpoly_eval x p =
    (\<Sum>m\<in>q4830725_polynomial_support p.
      p m * (\<Prod>v\<in>q4830725_monomial_support m. x v ^ m v))"

definition q4830725_is_ideal_on ::
    "'v set \<Rightarrow> ('v, 'a::comm_ring_1) q4830725_raw_mpoly set \<Rightarrow> bool" where
  "q4830725_is_ideal_on V I \<longleftrightarrow>
    (\<forall>p\<in>I. q4830725_is_mpoly_on V p) \<and>
    q4830725_mpoly_zero \<in> I \<and>
    (\<forall>p\<in>I. \<forall>q\<in>I. q4830725_mpoly_add p q \<in> I) \<and>
    (\<forall>p\<in>I. q4830725_mpoly_neg p \<in> I) \<and>
    (\<forall>a. q4830725_is_mpoly_on V a \<longrightarrow>
      (\<forall>p\<in>I. q4830725_mpoly_mul a p \<in> I))"

definition q4830725_coordinate_space ::
    "'v set \<Rightarrow> ('v \<Rightarrow> 'a::zero) set" where
  "q4830725_coordinate_space V = {x. \<forall>i. i \<notin> V \<longrightarrow> x i = 0}"

definition q4830725_zero_locus ::
    "'v set \<Rightarrow>
      ('v, 'a::comm_semiring_1) q4830725_raw_mpoly set \<Rightarrow>
      ('v \<Rightarrow> 'a) set" where
  "q4830725_zero_locus V I =
    {x\<in>q4830725_coordinate_space V.
      \<forall>p\<in>I. q4830725_mpoly_eval x p = 0}"

definition q4830725_poly_map ::
    "'v set \<Rightarrow>
      ('v \<Rightarrow> ('v, 'a::comm_semiring_1) q4830725_raw_mpoly) \<Rightarrow>
      ('v \<Rightarrow> 'a) \<Rightarrow> ('v \<Rightarrow> 'a)" where
  "q4830725_poly_map V p =
    (\<lambda>x i. if i \<in> V then q4830725_mpoly_eval x (p i) else 0)"

definition q4830725_is_algebraically_closed ::
    "'a::field itself \<Rightarrow> bool" where
  "q4830725_is_algebraically_closed _ \<longleftrightarrow>
    (\<forall>c :: nat \<Rightarrow> 'a.
      finite {n. c n \<noteq> 0} \<longrightarrow>
      (\<exists>n>0. c n \<noteq> 0) \<longrightarrow>
      (\<exists>x. (\<Sum>n\<in>{n. c n \<noteq> 0}. c n * x ^ n) = 0))"

theorem ax_grothendieck_zeroLocus:
  fixes V :: "'i set"
    and I :: "('i, 'K::field) q4830725_raw_mpoly set"
    and p :: "'i \<Rightarrow> ('i, 'K) q4830725_raw_mpoly"
  assumes algebraically_closed:
      "q4830725_is_algebraically_closed (TYPE('K))"
    and finite_coordinates: "finite V"
    and ideal_I: "q4830725_is_ideal_on V I"
    and polynomial_p: "\<forall>i\<in>V. q4830725_is_mpoly_on V (p i)"
  shows
    "let S = q4830725_zero_locus V I;
         F = q4830725_poly_map V p
     in F ` S \<subseteq> S \<longrightarrow>
        inj_on F S \<longrightarrow>
        S \<subseteq> F ` S"
  sorry

end
