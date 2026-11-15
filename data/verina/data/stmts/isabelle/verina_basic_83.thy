(*
  Statement-only formalization of VERINA corpus artifact verina_basic_83
  (verina__isabelle__verina_basic_83), catalog title "concat": an executable
  integer-array loop fills a newly allocated array with the first input
  followed by the second, together with its unconditional precondition,
  length-and-elements postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_83
  imports Main
begin

definition concat_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "concat_getBang xs i =
    (if i < length xs then xs ! i else 0)"

definition concat_setBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int list" where
  "concat_setBang xs i x =
    (if i < length xs then list_update xs i x else xs)"

definition concat_precond ::
    "int list \<Rightarrow> int list \<Rightarrow> bool" where
  "concat_precond a b \<longleftrightarrow> True"

definition concat_loop_step ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow>
      nat \<Rightarrow> int list" where
  "concat_loop_step a b c i =
    concat_setBang c i
      (if i < length a
       then concat_getBang a i
       else concat_getBang b (i - length a))"

definition concat_loop ::
    "int list \<Rightarrow> int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      int list \<Rightarrow> int list" where
  "concat_loop a b n i c =
    foldl (concat_loop_step a b) c [i..<n]"

definition concat :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "concat a b =
    (let n = length a + length b
     in concat_loop a b n 0 (replicate n 0))"

definition concat_postcond ::
    "int list \<Rightarrow> int list \<Rightarrow> int list \<Rightarrow> bool" where
  "concat_postcond a b result \<longleftrightarrow>
    length result = length a + length b \<and>
    (\<forall>k<length a.
      concat_getBang result k = concat_getBang a k) \<and>
    (\<forall>k<length b.
      concat_getBang result (k + length a) = concat_getBang b k)"

theorem concat_spec_satisfied:
  assumes "concat_precond a b"
  shows "concat_postcond a b (concat a b)"
  sorry

end
