(*
  Statement-only formalization of VERINA corpus artifact verina_basic_58
  (verina__isabelle__verina_basic_58), catalog title
  "double_array_elements": an executable integer-array loop doubles every
  element using the original array values, together with its unconditional
  precondition, size-and-pointwise postcondition, and final correctness
  proposition. This file contains no proof.
*)

theory verina_basic_58
  imports Main
begin

definition double_array_elements_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "double_array_elements_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition double_array_elements_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "double_array_elements_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition double_array_elements_precond :: "int list \<Rightarrow> bool" where
  "double_array_elements_precond s \<longleftrightarrow> True"

definition double_array_elements_step ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "double_array_elements_step s_old current i =
    double_array_elements_setBang current i
      (2 * double_array_elements_getBang s_old i)"

definition double_array_elements_aux ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> int list" where
  "double_array_elements_aux s_old s i =
    foldl (double_array_elements_step s_old) s [i..<length s]"

definition double_array_elements :: "int list \<Rightarrow> int list" where
  "double_array_elements s = double_array_elements_aux s s 0"

definition double_array_elements_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "double_array_elements_postcond s result \<longleftrightarrow>
    length result = length s \<and>
    (\<forall>i<length s.
      double_array_elements_getBang result i =
        2 * double_array_elements_getBang s i)"

theorem double_array_elements_spec_satisfied:
  assumes "double_array_elements_precond s"
  shows
    "double_array_elements_postcond s (double_array_elements s)"
  sorry

end
