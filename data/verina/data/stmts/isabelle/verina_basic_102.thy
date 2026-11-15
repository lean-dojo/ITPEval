(*
  Statement-only formalization of VERINA corpus artifact verina_basic_102,
  catalog title "twoSum": under the pair-existence precondition, an executable
  nested left-to-right scan returns the lexicographically first increasing
  pair of indices whose integer-array entries sum to the target, together with
  its full correctness contract. This file contains no proof.
*)

theory verina_basic_102
  imports Main
begin

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang nums i =
    (if i < length nums then nums ! i else 0)"

fun twoSum_pairwise_not_target :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "twoSum_pairwise_not_target [] target = True"
| "twoSum_pairwise_not_target (x # xs) target =
    (list_all (\<lambda>y. x + y \<noteq> target) xs \<and>
     twoSum_pairwise_not_target xs target)"

definition twoSum_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "twoSum_precond nums target \<longleftrightarrow>
    length nums > 1 \<and>
    \<not> twoSum_pairwise_not_target nums target"

fun twoSum_inner ::
    "int \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> nat
      \<Rightarrow> nat option" where
  "twoSum_inner x [] target j = None"
| "twoSum_inner x (y # ys) target j =
    (if x + y = target
     then Some j
     else twoSum_inner x ys target (j + 1))"

fun twoSum_outer ::
    "int list \<Rightarrow> int \<Rightarrow> nat
      \<Rightarrow> (nat \<times> nat) option" where
  "twoSum_outer [] target i = None"
| "twoSum_outer (x # xs) target i =
    (case twoSum_inner x xs target (i + 1) of
       Some j \<Rightarrow> Some (i, j)
     | None \<Rightarrow> twoSum_outer xs target (i + 1))"

definition twoSum :: "int list \<Rightarrow> int \<Rightarrow> (nat \<times> nat)" where
  "twoSum nums target =
    (case twoSum_outer nums target 0 of
       Some pair \<Rightarrow> pair
     | None \<Rightarrow> (0, 0))"

definition twoSum_zipIdx :: "'a list \<Rightarrow> ('a \<times> nat) list" where
  "twoSum_zipIdx xs = zip xs [0..<length xs]"

definition twoSum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool" where
  "twoSum_postcond nums target result \<longleftrightarrow>
    (let i = fst result;
         j = snd result
     in i < j \<and>
        j < length nums \<and>
        intList_getBang nums i + intList_getBang nums j = target \<and>
        list_all
          (\<lambda>(a, i').
            list_all
              (\<lambda>b. a + b \<noteq> target)
              (drop (i' + 1) nums))
          (twoSum_zipIdx (take i nums)) \<and>
        list_all
          (\<lambda>b. intList_getBang nums i + b \<noteq> target)
          (take (j - i - 1) (drop (i + 1) nums)))"

theorem twoSum_spec_satisfied:
  assumes "twoSum_precond nums target"
  shows "twoSum_postcond nums target (twoSum nums target)"
  sorry

end
