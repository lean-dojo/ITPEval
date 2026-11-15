(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_79,
  catalog title "twoSum": an executable nested left-to-right list search
  returns the lexicographically first pair of increasing indices whose integer
  values sum to the target, or None exactly when no such pair exists, together
  with its correctness contract. This file contains no proof.
*)

theory verina_advanced_79
  imports Main
begin

definition twoSum_precond :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "twoSum_precond nums target \<longleftrightarrow> True"

fun twoSum_inner ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> nat option" where
  "twoSum_inner [] j x target = None"
| "twoSum_inner (y # ys) j x target =
    (if x + y = target
     then Some j
     else twoSum_inner ys (j + 1) x target)"

fun twoSum_outer ::
    "int list \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> (nat \<times> nat) option" where
  "twoSum_outer [] i target = None"
| "twoSum_outer (x # xs) i target =
    (case twoSum_inner xs (i + 1) x target of
       Some j \<Rightarrow> Some (i, j)
     | None \<Rightarrow> twoSum_outer xs (i + 1) target)"

definition twoSum ::
    "int list \<Rightarrow> int \<Rightarrow> (nat \<times> nat) option" where
  "twoSum nums target = twoSum_outer nums 0 target"

definition intList_getBang :: "int list \<Rightarrow> nat \<Rightarrow> int" where
  "intList_getBang nums i =
    (if i < length nums then nums ! i else 0)"

fun twoSum_pairwise_not_target :: "int list \<Rightarrow> int \<Rightarrow> bool" where
  "twoSum_pairwise_not_target [] target = True"
| "twoSum_pairwise_not_target (x # xs) target =
    (list_all (\<lambda>y. x + y \<noteq> target) xs \<and>
     twoSum_pairwise_not_target xs target)"

definition twoSum_zipIdx :: "'a list \<Rightarrow> ('a \<times> nat) list" where
  "twoSum_zipIdx xs = zip xs [0..<length xs]"

definition twoSum_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> (nat \<times> nat) option \<Rightarrow> bool" where
  "twoSum_postcond nums target result \<longleftrightarrow>
    (case result of
       None \<Rightarrow> twoSum_pairwise_not_target nums target
     | Some pair \<Rightarrow>
         (let i = fst pair;
              j = snd pair
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
               (take (j - i - 1) (drop (i + 1) nums))))"

theorem twoSum_spec_satisfied:
  assumes "twoSum_precond nums target"
  shows "twoSum_postcond nums target (twoSum nums target)"
  sorry

end
