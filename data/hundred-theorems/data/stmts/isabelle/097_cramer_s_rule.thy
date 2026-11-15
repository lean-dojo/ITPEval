(*
  Statement-only formalization of Cramer's rule from Hundred Theorems
  item 097. It gives the unique solution of a nonsingular square linear
  system by column-replacement determinants. This file contains no proof.
*)

theory Cramers_Rule
  imports Complex_Main
begin

fun insert_everywhere :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list"
  where
    "insert_everywhere x [] = [[x]]"
  | "insert_everywhere x (y # ys) =
      (x # y # ys) # map ((#) y) (insert_everywhere x ys)"

fun list_permutations :: "'a list \<Rightarrow> 'a list list"
  where
    "list_permutations [] = [[]]"
  | "list_permutations (x # xs) =
      concat (map (insert_everywhere x) (list_permutations xs))"

definition inversion_count :: "nat list \<Rightarrow> nat"
  where
    "inversion_count p =
      card {(i, j). i < j \<and> j < length p \<and> p ! j < p ! i}"

definition permutation_sign :: "nat list \<Rightarrow> int"
  where
    "permutation_sign p = (if even (inversion_count p) then 1 else -1)"

definition list_determinant :: "'a::field list list \<Rightarrow> 'a"
  where
    "list_determinant A =
      (let n = length A
       in sum_list
         (map
           (\<lambda>p. of_int (permutation_sign p)
             * prod_list (map (\<lambda>i. (A ! i) ! (p ! i)) [0..<n]))
           (list_permutations [0..<n])))"

definition matrix_vector_product ::
    "'a::field list list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
    "matrix_vector_product A x =
      map (\<lambda>row. sum_list (map2 (*) row x)) A"

definition replace_matrix_column ::
    "'a::field list list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a list list"
  where
    "replace_matrix_column A b k =
      map
        (\<lambda>i. map
          (\<lambda>j. if j = k then b ! i else (A ! i) ! j)
          [0..<length A])
        [0..<length A]"

theorem hundred_theorems_cramer:
  fixes A :: "'a::field list list"
    and x b :: "'a list"
  assumes square: "\<forall>row \<in> set A. length row = length A"
    and x_dimension: "length x = length A"
    and b_dimension: "length b = length A"
    and nonsingular: "list_determinant A \<noteq> 0"
  shows
    "matrix_vector_product A x = b \<longleftrightarrow>
      x = map
        (\<lambda>k. list_determinant (replace_matrix_column A b k)
          / list_determinant A)
        [0..<length A]"
  sorry

end
