(*
  Statement-only formalization of VERINA corpus artifact verina_basic_87
  (verina__isabelle__verina_basic_87), catalog title "SelectionSort": an
  executable selection-sort program repeatedly finds a minimum index in the
  remaining integer-array suffix and swaps it into place, together with its
  unconditional precondition, sorted-permutation postcondition, and final
  correctness proposition. This file contains no proof.
*)

theory verina_basic_87
  imports Main
begin

definition SelectionSort_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "SelectionSort_getBang a i =
    (if i < length a then a ! i else 0)"

definition SelectionSort_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "SelectionSort_setBang a i x =
    (if i < length a then list_update a i x else a)"

definition SelectionSort_precond :: "int list \<Rightarrow> bool" where
  "SelectionSort_precond a \<longleftrightarrow> True"

definition findMinIndexInRange_step ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "findMinIndexInRange_step arr start minIdx i =
    (let currIdx = start + i
     in if SelectionSort_getBang arr currIdx <
           SelectionSort_getBang arr minIdx
        then currIdx
        else minIdx)"

definition findMinIndexInRange ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "findMinIndexInRange arr start finish =
    foldl (findMinIndexInRange_step arr start) start
      [0..<finish - start]"

definition SelectionSort_swap ::
    "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int list" where
  "SelectionSort_swap a i j =
    (if i < length a \<and> j < length a \<and> i \<noteq> j
     then
       (let temp = SelectionSort_getBang a i;
            a' = SelectionSort_setBang a i
              (SelectionSort_getBang a j)
        in SelectionSort_setBang a' j temp)
     else a)"

definition SelectionSort_step ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "SelectionSort_step arr i =
    (let minIdx = findMinIndexInRange arr i (length arr)
     in SelectionSort_swap arr i minIdx)"

definition SelectionSort :: "int list \<Rightarrow> int list" where
  "SelectionSort a =
    foldl SelectionSort_step a [0..<length a]"

fun SelectionSort_pairwise_le :: "int list \<Rightarrow> bool" where
  "SelectionSort_pairwise_le [] = True"
| "SelectionSort_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     SelectionSort_pairwise_le xs)"

definition SelectionSort_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "SelectionSort_postcond a result \<longleftrightarrow>
    SelectionSort_pairwise_le result \<and>
    (\<forall>z. count_list a z = count_list result z)"

theorem SelectionSort_spec_satisfied:
  fixes a :: "int list"
  assumes "SelectionSort_precond a"
  shows "SelectionSort_postcond a (SelectionSort a)"
  sorry

end
