(*
  Statement-only formalization of thousand-theorems corpus artifact Q656772
  (thousand-theorems__isabelle__Q656772), "Cayley-Hamilton theorem": over an
  arbitrary commutative ring, the characteristic polynomial of every square
  matrix on a finite index type annihilates that matrix. This file contains
  no proof.
*)

theory Q656772_cayley_hamilton_theorem
  imports Main
begin

type_synonym ('a, 'i) q656772_matrix = "'i \<Rightarrow> 'i \<Rightarrow> 'a"

definition q656772_zero_matrix ::
    "('a::zero, 'i) q656772_matrix" where
  "q656772_zero_matrix = (\<lambda>_ _. 0)"

definition q656772_identity_matrix ::
    "('a::{zero, one}, 'i) q656772_matrix" where
  "q656772_identity_matrix = (\<lambda>i j. if i = j then 1 else 0)"

definition q656772_matrix_mult ::
    "('a::semiring_0, 'i::finite) q656772_matrix \<Rightarrow>
      ('a, 'i) q656772_matrix \<Rightarrow> ('a, 'i) q656772_matrix" where
  "q656772_matrix_mult A B =
    (\<lambda>i j. \<Sum>k\<in>(UNIV :: 'i set). A i k * B k j)"

fun q656772_matrix_pow ::
    "('a::{semiring_0, monoid_mult}, 'i::finite) q656772_matrix \<Rightarrow> nat \<Rightarrow>
      ('a, 'i) q656772_matrix" where
  "q656772_matrix_pow A 0 = q656772_identity_matrix"
| "q656772_matrix_pow A (Suc k) =
    q656772_matrix_mult (q656772_matrix_pow A k) A"

definition q656772_scalar_mult ::
    "'a::semiring_0 \<Rightarrow> ('a, 'i) q656772_matrix \<Rightarrow>
      ('a, 'i) q656772_matrix" where
  "q656772_scalar_mult c A = (\<lambda>i j. c * A i j)"

definition q656772_index_list :: "'i::finite list" where
  "q656772_index_list =
    (SOME xs. distinct xs \<and> set xs = (UNIV :: 'i set))"

definition q656772_poly_one :: "nat \<Rightarrow> 'a::{zero, one}" where
  "q656772_poly_one = (\<lambda>n. if n = 0 then 1 else 0)"

definition q656772_poly_mult ::
    "(nat \<Rightarrow> 'a::semiring_0) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow>
      nat \<Rightarrow> 'a" where
  "q656772_poly_mult p q =
    (\<lambda>n. \<Sum>k\<le>n. p k * q (n - k))"

definition q656772_poly_scalar_mult ::
    "'a::semiring_0 \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "q656772_poly_scalar_mult c p = (\<lambda>n. c * p n)"

fun q656772_poly_sum_list ::
    "(nat \<Rightarrow> 'a::monoid_add) list \<Rightarrow> nat \<Rightarrow> 'a" where
  "q656772_poly_sum_list [] = (\<lambda>_. 0)"
| "q656772_poly_sum_list (p # ps) =
    (\<lambda>n. p n + q656772_poly_sum_list ps n)"

definition q656772_characteristic_entry ::
    "('a::{comm_ring, comm_monoid_mult}, 'i) q656772_matrix \<Rightarrow>
      'i \<Rightarrow> 'i \<Rightarrow> nat \<Rightarrow> 'a" where
  "q656772_characteristic_entry A i j =
    (\<lambda>n.
      if n = 0 then - A i j
      else if n = 1 \<and> i = j then 1
      else 0)"

fun q656772_poly_determinant_list ::
    "('a::{comm_ring, comm_monoid_mult}, 'i) q656772_matrix \<Rightarrow>
      'i list \<Rightarrow> 'i list \<Rightarrow> nat \<Rightarrow> 'a" where
  "q656772_poly_determinant_list A [] js = q656772_poly_one"
| "q656772_poly_determinant_list A (i # is) js =
    q656772_poly_sum_list
      (map
        (\<lambda>(k, j).
          q656772_poly_scalar_mult ((-1 :: 'a) ^ k)
            (q656772_poly_mult
              (q656772_characteristic_entry A i j)
              (q656772_poly_determinant_list A is (remove1 j js))))
        (zip [0..<length js] js))"

definition q656772_charpoly_coeff ::
    "('a::{comm_ring, comm_monoid_mult}, 'i::finite) q656772_matrix \<Rightarrow>
      nat \<Rightarrow> 'a" where
  "q656772_charpoly_coeff A =
    q656772_poly_determinant_list A
      q656772_index_list q656772_index_list"

definition q656772_eval_matrix ::
    "(nat \<Rightarrow> 'a::{comm_ring, comm_monoid_mult}) \<Rightarrow>
      ('a, 'i::finite) q656772_matrix \<Rightarrow> ('a, 'i) q656772_matrix" where
  "q656772_eval_matrix p A =
    (\<lambda>i j.
      \<Sum>k\<le>card (UNIV :: 'i set).
        p k * q656772_matrix_pow A k i j)"

theorem q656772_cayley_hamilton:
  fixes A :: "('a::{comm_ring, comm_monoid_mult}, 'i::finite) q656772_matrix"
  shows "q656772_eval_matrix (q656772_charpoly_coeff A) A =
    q656772_zero_matrix"
  sorry

end
