(*
  Statement-only formalization of VERINA corpus artifact verina_basic_106,
  catalog title "arraySum": an executable integer-array loop computes the
  element-wise sum of two equal-length arrays, together with its complete
  size and element correctness contract. This file contains no proof.
*)

theory verina_basic_106
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition intList_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "intList_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition arraySum_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "arraySum_precond a b \<longleftrightarrow>
    length a = length b"

definition arraySum_loop_step ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow>
      nat \<Rightarrow> int list" where
  "arraySum_loop_step a b c i =
    intList_setBang c i
      (intList_getBang a i + intList_getBang b i)"

definition loop ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int list \<Rightarrow> int list" where
  "loop a b n i c =
    foldl (arraySum_loop_step a b) c [i..<n]"

definition arraySum ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "arraySum a b =
    (let n = length a;
         c = replicate n 0
     in loop a b n 0 c)"

definition arraySum_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "arraySum_postcond a b result \<longleftrightarrow>
    length result = length a \<and>
    (\<forall>i<length a.
      intList_getBang a i + intList_getBang b i =
        intList_getBang result i)"

theorem arraySum_spec_satisfied:
  assumes "arraySum_precond a b"
  shows "arraySum_postcond a b (arraySum a b)"
  sorry

end
