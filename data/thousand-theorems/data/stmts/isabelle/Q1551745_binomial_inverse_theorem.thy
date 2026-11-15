(*
  Statement-only formalization of thousand-theorems corpus artifact Q1551745
  (thousand-theorems__isabelle__Q1551745), "Binomial inverse theorem": for
  rectangular matrices over an arbitrary possibly trivial unital ring, the
  inverse of A + U*C*V has the binomial inverse formula whenever A, the inner
  correction matrix, and A + U*C*V have chosen two-sided inverses. This file
  contains no proof.
*)

theory Q1551745_binomial_inverse_theorem
  imports Main
begin

type_synonym ('a, 'i, 'j) q1551745_matrix = "'i \<Rightarrow> 'j \<Rightarrow> 'a"

definition q1551745_matrix_add ::
    "('a::ring, 'i, 'j) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'j) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'j) q1551745_matrix" where
  "q1551745_matrix_add A B = (\<lambda>i j. A i j + B i j)"

definition q1551745_matrix_sub ::
    "('a::ring, 'i, 'j) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'j) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'j) q1551745_matrix" where
  "q1551745_matrix_sub A B = (\<lambda>i j. A i j - B i j)"

definition q1551745_matrix_mult ::
    "'j set \<Rightarrow>
      ('a::ring, 'i, 'j) q1551745_matrix \<Rightarrow>
      ('a, 'j, 'k) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'k) q1551745_matrix" where
  "q1551745_matrix_mult J A B =
    (\<lambda>i k. \<Sum>j\<in>J. A i j * B j k)"

definition q1551745_identity_matrix ::
    "'a::ring \<Rightarrow> 'i set \<Rightarrow>
      ('a, 'i, 'i) q1551745_matrix" where
  "q1551745_identity_matrix u I =
    (\<lambda>i j. if i \<in> I \<and> j \<in> I \<and> i = j then u else 0)"

definition q1551745_matrix_eq ::
    "'i set \<Rightarrow> 'j set \<Rightarrow>
      ('a, 'i, 'j) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'j) q1551745_matrix \<Rightarrow> bool" where
  "q1551745_matrix_eq I J A B \<longleftrightarrow>
    (\<forall>i\<in>I. \<forall>j\<in>J. A i j = B i j)"

definition q1551745_two_sided_inverse ::
    "'a::ring \<Rightarrow> 'i set \<Rightarrow>
      ('a, 'i, 'i) q1551745_matrix \<Rightarrow>
      ('a, 'i, 'i) q1551745_matrix \<Rightarrow> bool" where
  "q1551745_two_sided_inverse u I A Ainv \<longleftrightarrow>
    q1551745_matrix_eq I I
      (q1551745_matrix_mult I Ainv A)
      (q1551745_identity_matrix u I) \<and>
    q1551745_matrix_eq I I
      (q1551745_matrix_mult I A Ainv)
      (q1551745_identity_matrix u I)"

theorem q1551745_binomial_inverse:
  fixes u :: "'a::ring"
    and I :: "'n set"
    and J :: "'m set"
    and A :: "('a, 'n, 'n) q1551745_matrix"
    and U :: "('a, 'n, 'm) q1551745_matrix"
    and C :: "('a, 'm, 'm) q1551745_matrix"
    and V :: "('a, 'm, 'n) q1551745_matrix"
    and Ainv :: "('a, 'n, 'n) q1551745_matrix"
    and Dinv :: "('a, 'm, 'm) q1551745_matrix"
    and Einv :: "('a, 'n, 'n) q1551745_matrix"
  assumes left_unit: "\<And>x. u * x = x"
    and right_unit: "\<And>x. x * u = x"
    and finite_I: "finite I"
    and finite_J: "finite J"
    and inverse_A: "q1551745_two_sided_inverse u I A Ainv"
    and inverse_D:
      "q1551745_two_sided_inverse u J
        (q1551745_matrix_add C
          (q1551745_matrix_mult J
            (q1551745_matrix_mult I
              (q1551745_matrix_mult I
                (q1551745_matrix_mult J C V) Ainv) U) C))
        Dinv"
    and inverse_E:
      "q1551745_two_sided_inverse u I
        (q1551745_matrix_add A
          (q1551745_matrix_mult J
            (q1551745_matrix_mult J U C) V))
        Einv"
  shows
    "q1551745_matrix_eq I I Einv
      (q1551745_matrix_sub Ainv
        (q1551745_matrix_mult I
          (q1551745_matrix_mult J
            (q1551745_matrix_mult J
              (q1551745_matrix_mult J
                (q1551745_matrix_mult J
                  (q1551745_matrix_mult I Ainv U) C) Dinv) C) V)
          Ainv))"
  sorry

end
