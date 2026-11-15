(*
  Statement-only formalization of VERINA corpus artifact verina_basic_88
  (verina__isabelle__verina_basic_88), catalog title "ToArray": an executable
  conversion of an integer list to an immutable integer array preserving its
  length and every element in order, together with its unconditional
  precondition, postcondition, and final correctness proposition. This file
  contains no proof.
*)

theory verina_basic_88
  imports Main
begin

type_synonym lean_int_array = "int list"

definition ToArray_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "ToArray_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition ToArray_precond :: "int list \<Rightarrow> bool" where
  "ToArray_precond xs \<longleftrightarrow> True"

definition ToArray :: "int list \<Rightarrow> lean_int_array" where
  "ToArray xs = xs"

definition ToArray_postcond ::
    "int list \<Rightarrow> lean_int_array \<Rightarrow> bool" where
  "ToArray_postcond xs result \<longleftrightarrow>
    length result = length xs \<and>
    (\<forall>i. i < length xs \<longrightarrow>
      ToArray_getBang result i = ToArray_getBang xs i)"

theorem ToArray_spec_satisfied:
  fixes xs :: "int list"
  assumes "ToArray_precond xs"
  shows "ToArray_postcond xs (ToArray xs)"
  sorry

end
