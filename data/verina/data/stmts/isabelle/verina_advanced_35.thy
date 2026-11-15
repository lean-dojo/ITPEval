(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_35,
  catalog title "majorityElement": an executable frequency-table program
  returns the integer occurring strictly more than half the input-list length,
  under the assumption that such an integer exists, together with its
  correctness contract. This file contains no proof.
*)

theory verina_advanced_35
  imports Main
begin

definition majorityElement_precond :: "int list \<Rightarrow> bool" where
  "majorityElement_precond nums \<longleftrightarrow>
    nums \<noteq> [] \<and>
    list_ex
      (\<lambda>x. count_list nums x > length nums div 2)
      nums"

definition majorityElement_buildCounts ::
    "int list \<Rightarrow> int \<Rightarrow> nat" where
  "majorityElement_buildCounts nums =
    foldl
      (\<lambda>counts x. counts(x := counts x + 1))
      (\<lambda>_. 0)
      nums"

fun majorityElement_findKey ::
    "int list \<Rightarrow> (int \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> int"
    where
  "majorityElement_findKey [] counts half = 0"
| "majorityElement_findKey (x # xs) counts half =
    (if counts x > half
     then x
     else majorityElement_findKey xs counts half)"

definition majorityElement :: "int list \<Rightarrow> int" where
  "majorityElement nums =
    (let counts = majorityElement_buildCounts nums;
         keys = remdups nums
     in majorityElement_findKey keys counts (length nums div 2))"

definition majorityElement_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "majorityElement_postcond nums result \<longleftrightarrow>
    count_list nums result > length nums div 2 \<and>
    list_all
      (\<lambda>x. x \<noteq> result \<longrightarrow>
        count_list nums x \<le> length nums div 2)
      nums"

theorem majorityElement_spec_satisfied:
  assumes "majorityElement_precond nums"
  shows "majorityElement_postcond nums (majorityElement nums)"
  sorry

end
