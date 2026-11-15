(*
  Statement-only formalization of VERINA corpus artifact verina_basic_105,
  catalog title "arrayProduct": an executable integer-array loop computes the
  element-wise product of two equal-length arrays, together with its complete
  size and element correctness contract. This file contains no proof.
*)

theory verina_basic_105
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition intList_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "intList_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition arrayProduct_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "arrayProduct_precond a b \<longleftrightarrow>
    length a = length b"

definition arrayProduct_loop_step ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow>
      nat \<Rightarrow> int list" where
  "arrayProduct_loop_step a b c i =
    intList_setBang c i
      (intList_getBang a i * intList_getBang b i)"

definition loop ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int list \<Rightarrow> int list" where
  "loop a b len i c =
    foldl (arrayProduct_loop_step a b) c [i..<len]"

definition arrayProduct ::
    "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "arrayProduct a b =
    (let len = length a;
         c = replicate len 0
     in loop a b len 0 c)"

definition arrayProduct_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "arrayProduct_postcond a b result \<longleftrightarrow>
    length result = length a \<and>
    (\<forall>i<length a.
      intList_getBang a i * intList_getBang b i =
        intList_getBang result i)"

theorem arrayProduct_spec_satisfied:
  assumes "arrayProduct_precond a b"
  shows "arrayProduct_postcond a b (arrayProduct a b)"
  sorry

end
