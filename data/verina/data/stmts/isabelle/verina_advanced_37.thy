(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_37,
  catalog title "majorityElement": an executable insertion-sort program
  returns the middle integer of a nonempty list having a majority element,
  with a contract stating that the result is that majority element. This file
  contains no proof.
*)

theory verina_advanced_37
  imports Main
begin

definition majorityElement_precond :: "int list \<Rightarrow> bool" where
  "majorityElement_precond nums \<longleftrightarrow>
    length nums > 0 \<and>
    list_ex
      (\<lambda>x. count_list nums x > length nums div 2)
      nums"

fun majorityElement_insert :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "majorityElement_insert x [] = [x]"
| "majorityElement_insert x (h # t) =
    (if x \<le> h
     then x # h # t
     else h # majorityElement_insert x t)"

fun majorityElement_insertionSort :: "int list \<Rightarrow> int list" where
  "majorityElement_insertionSort [] = []"
| "majorityElement_insertionSort (h # t) =
    majorityElement_insert h (majorityElement_insertionSort t)"

fun majorityElement_getAt :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "majorityElement_getAt [] i = 0"
| "majorityElement_getAt (h # t) 0 = h"
| "majorityElement_getAt (h # t) (Suc i) = majorityElement_getAt t i"

definition majorityElement :: "int list \<Rightarrow> int" where
  "majorityElement nums =
    (let sorted = majorityElement_insertionSort nums;
         len = length sorted;
         mid = len div 2
     in majorityElement_getAt sorted mid)"

definition majorityElement_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "majorityElement_postcond nums result \<longleftrightarrow>
    (let n = length nums
     in count_list nums result > n div 2 \<and>
        list_all
          (\<lambda>x. x = result \<or> count_list nums x \<le> n div 2)
          nums)"

theorem majorityElement_spec_satisfied:
  assumes "majorityElement_precond nums"
  shows "majorityElement_postcond nums (majorityElement nums)"
  sorry

end
