(*
  Statement-only formalization of VERINA corpus artifact verina_basic_77
  (verina__isabelle__verina_basic_77), catalog title
  "modify_array_element": an executable nested-array update replaces one
  natural-number element while preserving both array sizes and every other
  inner array and element, together with its bounds precondition,
  postcondition, and final correctness proposition. This file contains no
  proof.
*)

theory verina_basic_77
  imports Main
begin

definition modify_array_element_getOuterBang ::
    "nat list list \<Rightarrow> nat \<Rightarrow> nat list" where
  "modify_array_element_getOuterBang arr index =
    (if index < length arr then arr ! index else [])"

definition modify_array_element_getInnerBang ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "modify_array_element_getInnerBang inner index =
    (if index < length inner then inner ! index else 0)"

definition modify_array_element_precond ::
    "nat list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
    where
  "modify_array_element_precond arr index1 index2 val \<longleftrightarrow>
    index1 < length arr \<and>
    index2 < length (modify_array_element_getOuterBang arr index1)"

definition updateInner ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "updateInner a idx val =
    (if idx < length a then list_update a idx val else a)"

definition modify_array_element_setOuterBang ::
    "nat list list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list list"
    where
  "modify_array_element_setOuterBang arr index inner =
    (if index < length arr then list_update arr index inner else arr)"

definition modify_array_element ::
    "nat list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat list list" where
  "modify_array_element arr index1 index2 val =
    (let inner = modify_array_element_getOuterBang arr index1;
         inner' = updateInner inner index2 val
     in modify_array_element_setOuterBang arr index1 inner')"

definition modify_array_element_postcond ::
    "nat list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat list list \<Rightarrow> bool" where
  "modify_array_element_postcond arr index1 index2 val result \<longleftrightarrow>
    length result = length arr \<and>
    length (modify_array_element_getOuterBang result index1) =
      length (modify_array_element_getOuterBang arr index1) \<and>
    (\<forall>i<length arr.
      i \<noteq> index1 \<longrightarrow>
      modify_array_element_getOuterBang result i =
        modify_array_element_getOuterBang arr i) \<and>
    (\<forall>j<length (modify_array_element_getOuterBang arr index1).
      j \<noteq> index2 \<longrightarrow>
      modify_array_element_getInnerBang
        (modify_array_element_getOuterBang result index1) j =
      modify_array_element_getInnerBang
        (modify_array_element_getOuterBang arr index1) j) \<and>
    modify_array_element_getInnerBang
      (modify_array_element_getOuterBang result index1) index2 = val"

theorem modify_array_element_spec_satisfied:
  fixes arr :: "nat list list"
    and index1 index2 val :: nat
  assumes "modify_array_element_precond arr index1 index2 val"
  shows
    "modify_array_element_postcond arr index1 index2 val
      (modify_array_element arr index1 index2 val)"
  sorry

end
