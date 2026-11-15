(*
  Statement-only formalization of VERINA corpus artifact verina_basic_34
  (verina__isabelle__verina_basic_34), catalog title "findEvenNumbers": an
  executable integer-array fold retains exactly the even entries in input
  order, together with its unconditional precondition, multiplicity and order
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_34
  imports Main
begin

definition isEven :: "int \<Rightarrow> bool" where
  "isEven n = (n mod 2 = 0)"

definition findEvenNumbers_precond :: "int list \<Rightarrow> bool" where
  "findEvenNumbers_precond arr \<longleftrightarrow> True"

definition findEvenNumbers :: "int list \<Rightarrow> int list" where
  "findEvenNumbers arr =
    foldl
      (\<lambda>acc x. if isEven x then acc @ [x] else acc)
      []
      arr"

fun findEvenNumbers_idxOf :: "int list \<Rightarrow> int \<Rightarrow> nat" where
  "findEvenNumbers_idxOf [] x = 0"
| "findEvenNumbers_idxOf (y # ys) x =
    (if y = x then 0 else Suc (findEvenNumbers_idxOf ys x))"

definition findEvenNumbers_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "findEvenNumbers_postcond arr result \<longleftrightarrow>
    list_all
      (\<lambda>x.
        isEven x \<and>
        x \<in> set arr \<and>
        count_list result x = count_list arr x)
      result \<and>
    list_all
      (\<lambda>x. isEven x \<longrightarrow> x \<in> set result)
      arr \<and>
    list_all
      (\<lambda>x.
        list_all
          (\<lambda>y.
            isEven x \<longrightarrow>
            isEven y \<longrightarrow>
            findEvenNumbers_idxOf arr x \<le>
              findEvenNumbers_idxOf arr y \<longrightarrow>
            findEvenNumbers_idxOf result x \<le>
              findEvenNumbers_idxOf result y)
          arr)
      arr"

theorem findEvenNumbers_spec_satisfied:
  assumes "findEvenNumbers_precond arr"
  shows
    "findEvenNumbers_postcond arr (findEvenNumbers arr)"
  sorry

end
