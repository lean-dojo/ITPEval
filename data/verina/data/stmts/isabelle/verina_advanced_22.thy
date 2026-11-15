(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_22,
  catalog title "isPeakValley": an executable integer-list program recognizes
  a nonempty strictly increasing phase followed by a nonempty strictly
  decreasing phase, together with its precondition and peak-index Boolean
  contract. This file contains no proof.
*)

theory verina_advanced_22
  imports Main
begin

definition isPeakValley_precond :: "int list \<Rightarrow> bool" where
  "isPeakValley_precond lst \<longleftrightarrow> True"

fun isPeakValley_aux ::
    "int list \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "isPeakValley_aux (x # y # rest) increasing startedDecreasing =
    (if x < y
     then
       (if startedDecreasing
        then False
        else isPeakValley_aux (y # rest) True startedDecreasing)
     else if x > y
     then
       (if increasing
        then isPeakValley_aux (y # rest) increasing True
        else False)
     else False)"
| "isPeakValley_aux l increasing startedDecreasing =
    (increasing \<and> startedDecreasing)"

definition isPeakValley :: "int list \<Rightarrow> bool" where
  "isPeakValley lst = isPeakValley_aux lst False False"

definition int_list_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "int_list_getBang lst i =
    (if i < length lst then lst ! i else 0)"

definition isPeakValley_validPeaks :: "int list \<Rightarrow> nat list" where
  "isPeakValley_validPeaks lst =
    (let len = length lst
     in filter
       (\<lambda>p.
         1 \<le> p \<and>
         p < len - 1 \<and>
         list_all
           (\<lambda>i. int_list_getBang lst i <
             int_list_getBang lst (i + 1))
           [0..<p] \<and>
         list_all
           (\<lambda>i. int_list_getBang lst (p + i) >
             int_list_getBang lst (p + i + 1))
           [0..<(len - 1 - p)])
       [0..<len])"

definition isPeakValley_postcond ::
    "int list \<Rightarrow> bool \<Rightarrow> bool" where
  "isPeakValley_postcond lst result \<longleftrightarrow>
    (let validPeaks = isPeakValley_validPeaks lst
     in (validPeaks \<noteq> [] \<longrightarrow> result) \<and>
        (length validPeaks = 0 \<longrightarrow> \<not> result))"

theorem isPeakValley_spec_satisfied:
  assumes "isPeakValley_precond lst"
  shows "isPeakValley_postcond lst (isPeakValley lst)"
  sorry

end
