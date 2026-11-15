(*
  Statement-only formalization of VERINA corpus artifact verina_basic_20,
  catalog title "uniqueProduct": an executable integer-array program scans
  left to right and multiplies each distinct value only on its first
  occurrence, together with its trivial precondition, duplicate-removal
  postcondition, and correctness contract. This file contains no proof.
*)

theory verina_basic_20
  imports Main
begin

definition uniqueProduct_precond :: "int list \<Rightarrow> bool" where
  "uniqueProduct_precond arr \<longleftrightarrow> True"

fun uniqueProduct_loop ::
    "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int" where
  "uniqueProduct_loop [] seen product = product"
| "uniqueProduct_loop (x # xs) seen product =
    (if x \<in> set seen
     then uniqueProduct_loop xs seen product
     else uniqueProduct_loop xs (x # seen) (product * x))"

definition uniqueProduct :: "int list \<Rightarrow> int" where
  "uniqueProduct arr = uniqueProduct_loop arr [] 1"

definition uniqueProduct_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "uniqueProduct_postcond arr result \<longleftrightarrow>
    (let expected = foldl (\<lambda>acc x. acc * x) 1 (remdups arr)
     in result - expected = 0 \<and> expected - result = 0)"

theorem uniqueProduct_spec_satisfied:
  assumes "uniqueProduct_precond arr"
  shows "uniqueProduct_postcond arr (uniqueProduct arr)"
  sorry

end
