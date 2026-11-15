(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_76,
  catalog title "topKFrequent": an executable stable frequency-counting and
  insertion-sorting program returns the k most frequent distinct integers,
  together with its precondition and full correctness contract. This file
  contains no proof.
*)

theory verina_advanced_76
  imports Main
begin

definition topKFrequent_precond ::
    "int list \<Rightarrow> nat \<Rightarrow> bool" where
  "topKFrequent_precond nums k \<longleftrightarrow>
    k \<le> length (remdups nums)"

definition topKFrequent_freqStep ::
    "(int \<times> nat) list \<Rightarrow> int \<Rightarrow>
      (int \<times> nat) list" where
  "topKFrequent_freqStep acc n =
    (if list_ex (\<lambda>entry. fst entry = n) acc
     then
       map
         (\<lambda>entry.
           if fst entry = n
           then (fst entry, snd entry + 1)
           else entry)
         acc
     else acc @ [(n, 1)])"

definition topKFrequent_freqList ::
    "int list \<Rightarrow> (int \<times> nat) list" where
  "topKFrequent_freqList nums =
    foldl topKFrequent_freqStep [] nums"

fun topKFrequent_insertSorted ::
    "(int \<times> nat) \<Rightarrow> (int \<times> nat) list \<Rightarrow>
      (int \<times> nat) list" where
  "topKFrequent_insertSorted pair [] = [pair]"
| "topKFrequent_insertSorted pair ((y, cy) # ys) =
    (if snd pair > cy
     then pair # (y, cy) # ys
     else (y, cy) # topKFrequent_insertSorted pair ys)"

definition topKFrequent_sorted ::
    "int list \<Rightarrow> (int \<times> nat) list" where
  "topKFrequent_sorted nums =
    foldl
      (\<lambda>acc pair. topKFrequent_insertSorted pair acc)
      [] (topKFrequent_freqList nums)"

definition topKFrequent ::
    "int list \<Rightarrow> nat \<Rightarrow> int list" where
  "topKFrequent nums k =
    map fst (take k (topKFrequent_sorted nums))"

definition topKFrequent_zipIdx ::
    "int list \<Rightarrow> (int \<times> nat) list" where
  "topKFrequent_zipIdx xs = zip xs [0..<length xs]"

fun topKFrequent_pairwiseIndexed ::
    "int list \<Rightarrow> (int \<times> nat) list \<Rightarrow> bool" where
  "topKFrequent_pairwiseIndexed nums [] = True"
| "topKFrequent_pairwiseIndexed nums (p # ps) =
    (list_all
       (\<lambda>q.
         snd p < snd q \<longrightarrow>
         count_list nums (fst p) \<ge> count_list nums (fst q))
       ps \<and>
     topKFrequent_pairwiseIndexed nums ps)"

definition topKFrequent_postcond ::
    "int list \<Rightarrow> nat \<Rightarrow> int list \<Rightarrow> bool" where
  "topKFrequent_postcond nums k result \<longleftrightarrow>
    length result = k \<and>
    list_all (\<lambda>x. x \<in> set nums) result \<and>
    distinct result \<and>
    list_all
      (\<lambda>x.
        list_all
          (\<lambda>y.
            y \<in> set result \<or>
            count_list nums x \<ge> count_list nums y)
          nums)
      result \<and>
    topKFrequent_pairwiseIndexed nums (topKFrequent_zipIdx result)"

theorem topKFrequent_spec_satisfied:
  assumes "topKFrequent_precond nums k"
  shows "topKFrequent_postcond nums k (topKFrequent nums k)"
  sorry

end
