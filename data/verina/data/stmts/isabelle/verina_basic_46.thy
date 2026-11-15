(*
  Statement-only formalization of VERINA corpus artifact verina_basic_46
  (verina__isabelle__verina_basic_46), catalog title "lastPosition": an
  executable left-to-right scan of a pairwise nondecreasing integer array
  returns the last target index, or -1 when the target is absent, together
  with its precondition, postcondition, and final correctness proposition.
  This file contains no proof.
*)

theory verina_basic_46
  imports Main
begin

definition lastPosition_getBang ::
    "int list \<Rightarrow> nat \<Rightarrow> int" where
  "lastPosition_getBang arr i =
    (if i < length arr then arr ! i else 0)"

fun lastPosition_pairwise_le :: "int list \<Rightarrow> bool" where
  "lastPosition_pairwise_le [] = True"
| "lastPosition_pairwise_le (x # xs) =
    (list_all (\<lambda>y. x \<le> y) xs \<and>
     lastPosition_pairwise_le xs)"

definition lastPosition_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "lastPosition_precond arr elem \<longleftrightarrow>
    lastPosition_pairwise_le arr"

fun lastPosition_loop ::
    "int list \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "lastPosition_loop [] elem i pos = pos"
| "lastPosition_loop (a # rest) elem i pos =
    (if a = elem
     then lastPosition_loop rest elem (i + 1) (int i)
     else lastPosition_loop rest elem (i + 1) pos)"

definition lastPosition :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "lastPosition arr elem = lastPosition_loop arr elem 0 (-1)"

definition lastPosition_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "lastPosition_postcond arr elem result \<longleftrightarrow>
    (result = -1 \<or> result \<ge> 0) \<and>
    (result \<ge> 0 \<longrightarrow>
      nat result < length arr \<and>
      lastPosition_getBang arr (nat result) = elem \<and>
      list_all
        (\<lambda>x. x \<noteq> elem)
        (drop (nat result + 1) arr)) \<and>
    (result = -1 \<longrightarrow>
      list_all (\<lambda>x. x \<noteq> elem) arr)"

theorem lastPosition_spec_satisfied:
  assumes "lastPosition_precond arr elem"
  shows
    "lastPosition_postcond arr elem (lastPosition arr elem)"
  sorry

end
