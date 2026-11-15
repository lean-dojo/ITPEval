(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_61,
  catalog title "productExceptSelf": executable prefix- and suffix-product
  folds compute, at every integer-list index, the product of all other
  entries, together with the precondition and correctness contract. This file
  contains no proof.
*)

theory verina_advanced_61
  imports Main
begin

definition productExceptSelf_precond :: "int list \<Rightarrow> bool" where
  "productExceptSelf_precond nums \<longleftrightarrow> True"

definition computepref :: "int list \<Rightarrow> int list" where
  "computepref nums =
    foldl (\<lambda>acc x. acc @ [last acc * x]) [1] nums"

definition computeSuffix :: "int list \<Rightarrow> int list" where
  "computeSuffix nums =
    rev (foldl (\<lambda>acc x. acc @ [last acc * x]) [1] (rev nums))"

definition productExceptSelf :: "int list \<Rightarrow> int list" where
  "productExceptSelf nums =
    (let n = length nums
     in if n = 0
        then []
        else
          let pref = computepref nums;
              suffix = computeSuffix nums
          in map (\<lambda>i. pref ! i * suffix ! (i + 1)) [0..<n])"

fun productExceptSelf_myprod :: "int list \<Rightarrow> int" where
  "productExceptSelf_myprod [] = 1"
| "productExceptSelf_myprod (x # xs) =
    x * productExceptSelf_myprod xs"

definition productExceptSelf_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "productExceptSelf_postcond nums result \<longleftrightarrow>
    length nums = length result \<and>
    list_all
      (\<lambda>i.
        result ! i =
          productExceptSelf_myprod (take i nums) *
          productExceptSelf_myprod (drop (i + 1) nums))
      [0..<length nums]"

theorem productExceptSelf_spec_satisfied:
  assumes "productExceptSelf_precond nums"
  shows "productExceptSelf_postcond nums (productExceptSelf nums)"
  sorry

end
