(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_47,
  catalog title "mergeIntervals": an executable insertion sort orders integer
  intervals by start point and an accumulator-based scan merges overlaps,
  together with the valid-interval precondition and the coverage, separation,
  endpoint, and no-spurious-gap postcondition. This file contains no proof.
*)

theory verina_advanced_47
  imports Main
begin

definition mergeIntervals_precond :: "(int \<times> int) list \<Rightarrow> bool" where
  "mergeIntervals_precond intervals \<longleftrightarrow>
    list_all (\<lambda>(s, e). s \<le> e) intervals"

fun mergeIntervals_insert ::
    "(int \<times> int) \<Rightarrow>
     (int \<times> int) list \<Rightarrow>
     (int \<times> int) list" where
  "mergeIntervals_insert x [] = [x]"
| "mergeIntervals_insert x (y # ys) =
    (if fst x \<le> fst y
     then x # y # ys
     else y # mergeIntervals_insert x ys)"

fun mergeIntervals_sort ::
    "(int \<times> int) list \<Rightarrow> (int \<times> int) list" where
  "mergeIntervals_sort [] = []"
| "mergeIntervals_sort (x # xs) =
    mergeIntervals_insert x (mergeIntervals_sort xs)"

fun mergeIntervals_merge ::
    "(int \<times> int) list \<Rightarrow>
     (int \<times> int) list \<Rightarrow>
     (int \<times> int) list" where
  "mergeIntervals_merge [] acc = rev acc"
| "mergeIntervals_merge ((s, e) # rest) [] =
    mergeIntervals_merge rest [(s, e)]"
| "mergeIntervals_merge ((s, e) # rest) ((ps, pe) # accTail) =
    (if s \<le> pe
     then mergeIntervals_merge rest ((ps, max pe e) # accTail)
     else mergeIntervals_merge rest ((s, e) # (ps, pe) # accTail))"

definition mergeIntervals ::
    "(int \<times> int) list \<Rightarrow> (int \<times> int) list" where
  "mergeIntervals intervals =
    mergeIntervals_merge (mergeIntervals_sort intervals) []"

fun mergeIntervals_noOverlap :: "(int \<times> int) list \<Rightarrow> bool" where
  "mergeIntervals_noOverlap [] = True"
| "mergeIntervals_noOverlap [x] = True"
| "mergeIntervals_noOverlap ((s1, e1) # (s2, e2) # rest) =
    (e1 < s2 \<and>
     mergeIntervals_noOverlap ((s2, e2) # rest))"

definition mergeIntervals_postcond ::
    "(int \<times> int) list \<Rightarrow>
     (int \<times> int) list \<Rightarrow>
     bool" where
  "mergeIntervals_postcond intervals result \<longleftrightarrow>
    (let covered =
       list_all
         (\<lambda>(s, e).
           list_ex (\<lambda>(rs, re). rs \<le> s \<and> e \<le> re) result)
         intervals;
         resultBounded =
       list_all
         (\<lambda>(rs, re).
           list_ex (\<lambda>(s, e). s = rs) intervals \<and>
           list_ex (\<lambda>(s, e). e = re) intervals)
         result;
         noSpuriousMerge =
       list_all
         (\<lambda>(rs, re).
           list_all
             (\<lambda>(s, e).
               s = rs \<or>
               list_ex
                 (\<lambda>(s2, e2).
                   rs \<le> s2 \<and> e2 \<le> re \<and>
                   s2 < s \<and> e2 \<ge> s)
                 intervals)
             (filter
               (\<lambda>(s, e). rs \<le> s \<and> e \<le> re)
               intervals))
         result
     in covered \<and>
        mergeIntervals_noOverlap result \<and>
        resultBounded \<and>
        noSpuriousMerge)"

theorem mergeIntervals_spec_satisfied:
  assumes "mergeIntervals_precond intervals"
  shows
    "mergeIntervals_postcond
      intervals (mergeIntervals intervals)"
  sorry

end
