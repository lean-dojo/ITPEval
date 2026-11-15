(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_55,
  catalog title "mostFrequent": an executable frequency-map fold returns the
  most frequent integer in a nonempty list, breaking ties by first occurrence,
  together with its complete correctness contract. This file contains no proof.
*)

theory verina_advanced_55
  imports Main
begin

definition mostFrequent_precond :: "int list \<Rightarrow> bool" where
  "mostFrequent_precond xs \<longleftrightarrow> xs \<noteq> []"

fun countMap_insert ::
    "int \<Rightarrow> (int \<times> nat) list \<Rightarrow> (int \<times> nat) list" where
  "countMap_insert x [] = [(x, 1)]"
| "countMap_insert x ((k, n) # entries) =
    (if k = x
     then (k, n + 1) # entries
     else (k, n) # countMap_insert x entries)"

definition countMap :: "int list \<Rightarrow> (int \<times> nat) list" where
  "countMap xs = foldl (\<lambda>m x. countMap_insert x m) [] xs"

definition getMaxFrequency :: "(int \<times> nat) list \<Rightarrow> nat" where
  "getMaxFrequency m =
    foldl (\<lambda>acc entry. if snd entry > acc then snd entry else acc) 0 m"

definition getCandidates ::
    "(int \<times> nat) list \<Rightarrow> nat \<Rightarrow> int list" where
  "getCandidates m maxFreq =
    map fst (filter (\<lambda>entry. snd entry = maxFreq) m)"

fun getFirstWithFreq :: "int list \<Rightarrow> int list \<Rightarrow> int" where
  "getFirstWithFreq [] candidates = 0"
| "getFirstWithFreq (x # xs) candidates =
    (if x \<in> set candidates
     then x
     else getFirstWithFreq xs candidates)"

definition mostFrequent :: "int list \<Rightarrow> int" where
  "mostFrequent xs =
    (let freqMap = countMap xs;
         maxF = getMaxFrequency freqMap;
         candidates = getCandidates freqMap maxF
     in getFirstWithFreq xs candidates)"

fun listHeadOption :: "'a list \<Rightarrow> 'a option" where
  "listHeadOption [] = None"
| "listHeadOption (x # xs) = Some x"

definition mostFrequent_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "mostFrequent_postcond xs result \<longleftrightarrow>
    result \<in> set xs \<and>
    list_all
      (\<lambda>x. count_list xs x \<le> count_list xs result)
      xs \<and>
    listHeadOption
      (filter
        (\<lambda>x. count_list xs x = count_list xs result)
        xs) =
      Some result"

theorem mostFrequent_spec_satisfied:
  assumes "mostFrequent_precond xs"
  shows "mostFrequent_postcond xs (mostFrequent xs)"
  sorry

end
