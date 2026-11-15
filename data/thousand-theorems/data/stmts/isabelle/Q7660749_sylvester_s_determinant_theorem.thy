(*
  Statement-only formalization of thousand-theorems corpus artifact Q7660749
  (thousand-theorems__isabelle__Q7660749), "Sylvester's determinant theorem":
  over a possibly trivial unital commutative ring, det(I + AB) equals
  det(I + BA) for rectangular matrices on finite, possibly empty, index
  carriers. This file contains no proof.
*)

theory Q7660749_sylvester_s_determinant_theorem
  imports Main
begin

type_synonym ('a, 'i, 'j) q7660749_matrix = "'i \<Rightarrow> 'j \<Rightarrow> 'a"

definition q7660749_matrix_add ::
    "('a::comm_ring, 'i, 'j) q7660749_matrix \<Rightarrow>
      ('a, 'i, 'j) q7660749_matrix \<Rightarrow> ('a, 'i, 'j) q7660749_matrix" where
  "q7660749_matrix_add A B = (\<lambda>i j. A i j + B i j)"

definition q7660749_matrix_mult ::
    "'j set \<Rightarrow>
      ('a::comm_ring, 'i, 'j) q7660749_matrix \<Rightarrow>
      ('a, 'j, 'k) q7660749_matrix \<Rightarrow> ('a, 'i, 'k) q7660749_matrix" where
  "q7660749_matrix_mult J A B =
    (\<lambda>i k. \<Sum>j\<in>J. A i j * B j k)"

definition q7660749_identity_matrix ::
    "'a::comm_ring \<Rightarrow> 'i set \<Rightarrow>
      ('a, 'i, 'i) q7660749_matrix" where
  "q7660749_identity_matrix u I =
    (\<lambda>i j. if i \<in> I \<and> j \<in> I \<and> i = j then u else 0)"

definition q7660749_index_list :: "'i set \<Rightarrow> 'i list" where
  "q7660749_index_list I =
    (SOME xs. distinct xs \<and> set xs = I)"

fun q7660749_determinant_list ::
    "'a::comm_ring \<Rightarrow>
      ('a, 'i, 'i) q7660749_matrix \<Rightarrow>
      'i list \<Rightarrow> 'i list \<Rightarrow> 'a" where
  "q7660749_determinant_list u M [] js = u"
| "q7660749_determinant_list u M (i # is) js =
    sum_list
      (map
        (\<lambda>(k, j).
          (if even k then u else -u) * M i j *
            q7660749_determinant_list u M is (remove1 j js))
        (zip [0..<length js] js))"

definition q7660749_determinant ::
    "'a::comm_ring \<Rightarrow> 'i set \<Rightarrow>
      ('a, 'i, 'i) q7660749_matrix \<Rightarrow> 'a" where
  "q7660749_determinant u I M =
    q7660749_determinant_list u M
      (q7660749_index_list I) (q7660749_index_list I)"

theorem q7660749_sylvester_determinant:
  fixes u :: "'a::comm_ring"
    and I :: "'m set"
    and J :: "'n set"
    and A :: "('a, 'm, 'n) q7660749_matrix"
    and B :: "('a, 'n, 'm) q7660749_matrix"
  assumes unit: "\<And>x. u * x = x"
    and finite_I: "finite I"
    and finite_J: "finite J"
  shows
    "q7660749_determinant u I
        (q7660749_matrix_add (q7660749_identity_matrix u I)
          (q7660749_matrix_mult J A B)) =
      q7660749_determinant u J
        (q7660749_matrix_add (q7660749_identity_matrix u J)
          (q7660749_matrix_mult I B A))"
  sorry

end
