(*
  Statement-only formalization of thousand-theorems corpus artifact Q978688
  (thousand-theorems__isabelle__Q978688), "Gershgorin circle theorem": every
  eigenvalue of a finite square matrix over an arbitrary normed field satisfies
  the closed-ball norm inequality centered at some diagonal entry, with radius
  the sum of the norms of the off-diagonal entries in that row. This file
  contains no proof.
*)

theory Q978688_gershgorin_circle_theorem
  imports Complex_Main
begin

type_synonym ('a, 'i) q978688_matrix = "'i \<Rightarrow> 'i \<Rightarrow> 'a"

definition q978688_normed_field ::
    "('a::field \<Rightarrow> real) \<Rightarrow> bool"
  where
    "q978688_normed_field knorm \<longleftrightarrow>
      knorm 0 = 0 \<and>
      (\<forall>a. 0 \<le> knorm a) \<and>
      (\<forall>a. knorm a = 0 \<longleftrightarrow> a = 0) \<and>
      (\<forall>a. knorm (-a) = knorm a) \<and>
      (\<forall>a b. knorm (a + b) \<le> knorm a + knorm b) \<and>
      (\<forall>a b. knorm (a * b) = knorm a * knorm b)"

definition q978688_has_eigenvalue ::
    "('a::field, 'i::finite) q978688_matrix \<Rightarrow> 'a \<Rightarrow> bool"
  where
    "q978688_has_eigenvalue A mu \<longleftrightarrow>
      (\<exists>v :: 'i \<Rightarrow> 'a.
        v \<noteq> (\<lambda>_. 0) \<and>
        (\<forall>i. (\<Sum>j\<in>UNIV. A i j * v j) = mu * v i))"

theorem eigenvalue_mem_ball:
  fixes knorm :: "'a::field \<Rightarrow> real"
    and A :: "('a, 'i::finite) q978688_matrix"
    and mu :: 'a
  assumes normed_field: "q978688_normed_field knorm"
    and eigenvalue: "q978688_has_eigenvalue A mu"
  shows "\<exists>k.
    knorm (mu - A k k) \<le> (\<Sum>j\<in>UNIV - {k}. knorm (A k j))"
  sorry

end
