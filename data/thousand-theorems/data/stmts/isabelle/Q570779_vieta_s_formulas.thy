(*
  Statement-only formalization of the thousand-theorems corpus artifact Q570779
  (thousand-theorems__isabelle__Q570779), "Vieta's formulas": over an arbitrary
  commutative semiring, the product of the linear polynomials X + a indexed by
  a multiset expands as the sum of its elementary symmetric sums times the
  corresponding powers of X. This file contains no proof.
*)

theory Q570779_vieta_s_formulas
  imports Main
begin

type_synonym 'a q570779_poly = "nat \<Rightarrow> 'a"

definition q570779_poly_one ::
    "'a::{comm_semiring_0,comm_monoid_mult} q570779_poly" where
  "q570779_poly_one = (\<lambda>n. if n = 0 then 1 else 0)"

definition q570779_poly_mul ::
    "'a::comm_semiring_0 q570779_poly \<Rightarrow>
      'a q570779_poly \<Rightarrow> 'a q570779_poly" where
  "q570779_poly_mul p q =
    (\<lambda>n. \<Sum>i\<le>n. p i * q (n - i))"

primrec q570779_poly_pow ::
    "'a::{comm_semiring_0,comm_monoid_mult} q570779_poly \<Rightarrow>
      nat \<Rightarrow> 'a q570779_poly" where
  "q570779_poly_pow p 0 = q570779_poly_one"
| "q570779_poly_pow p (Suc n) =
    q570779_poly_mul p (q570779_poly_pow p n)"

definition q570779_linear ::
    "'a::comm_semiring_0 \<Rightarrow> 'a \<Rightarrow> 'a q570779_poly" where
  "q570779_linear a b =
    (\<lambda>n. if n = 0 then a else if n = 1 then b else 0)"

definition q570779_mset_prod ::
    "('a::{comm_semiring_0,comm_monoid_mult} \<Rightarrow> nat) \<Rightarrow>
      ('a \<Rightarrow> 'a q570779_poly) \<Rightarrow> 'a q570779_poly" where
  "q570779_mset_prod s f =
    Finite_Set.fold
      (\<lambda>a p. q570779_poly_mul (q570779_poly_pow (f a) (s a)) p)
      q570779_poly_one {a. 0 < s a}"

definition q570779_mset_size :: "('a \<Rightarrow> nat) \<Rightarrow> nat" where
  "q570779_mset_size s = (\<Sum>a\<in>{a. 0 < s a}. s a)"

definition q570779_nat_cast ::
    "nat \<Rightarrow> 'a::{comm_semiring_0,comm_monoid_mult}" where
  "q570779_nat_cast n = (\<Sum>i<n. 1)"

definition q570779_mset_esymm ::
    "('a::{comm_semiring_0,comm_monoid_mult} \<Rightarrow> nat) \<Rightarrow>
      nat \<Rightarrow> 'a" where
  "q570779_mset_esymm s j =
    (\<Sum>t |
      (\<forall>a. t a \<le> s a) \<and>
      (\<Sum>a\<in>{a. 0 < s a}. t a) = j.
        q570779_nat_cast
          (\<Prod>a\<in>{a. 0 < s a}. s a choose t a) *
        (\<Prod>a\<in>{a. 0 < s a}. a ^ t a))"

theorem Multiset_prod_X_add_C_eq_sum_esymm:
  fixes s :: "'a::{comm_semiring_0,comm_monoid_mult} \<Rightarrow> nat"
  assumes finite_support: "finite {a. 0 < s a}"
  shows "\<forall>n.
    q570779_mset_prod s (\<lambda>a. q570779_linear a 1) n =
      (\<Sum>j<q570779_mset_size s + 1.
        q570779_poly_mul
          (q570779_linear (q570779_mset_esymm s j) 0)
          (q570779_poly_pow (q570779_linear 0 1)
            (q570779_mset_size s - j)) n)"
  sorry

end
