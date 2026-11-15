(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_38,
  catalog title "maxCoverageAfterRemovingOne": an executable interval-list
  program removes each interval in turn, merges the remainder by increasing
  start point, and returns the maximum resulting natural-number coverage,
  together with its maximality contract. This file contains no proof.
*)

theory verina_advanced_38
  imports Main
begin

definition maxCoverageAfterRemovingOne_precond ::
    "(nat \<times> nat) list \<Rightarrow> bool" where
  "maxCoverageAfterRemovingOne_precond intervals \<longleftrightarrow>
    length intervals > 0"

fun maxCoverageAfterRemovingOne_eraseIdx ::
    "'a list \<Rightarrow> nat \<Rightarrow> 'a list" where
  "maxCoverageAfterRemovingOne_eraseIdx [] i = []"
| "maxCoverageAfterRemovingOne_eraseIdx (x # xs) 0 = xs"
| "maxCoverageAfterRemovingOne_eraseIdx (x # xs) (Suc i) =
    x # maxCoverageAfterRemovingOne_eraseIdx xs i"

fun maxCoverageAfterRemovingOne_insert ::
    "(nat \<times> nat) \<Rightarrow>
     (nat \<times> nat) list \<Rightarrow>
     (nat \<times> nat) list" where
  "maxCoverageAfterRemovingOne_insert current [] = [current]"
| "maxCoverageAfterRemovingOne_insert current (x # xs) =
    (if fst current \<le> fst x
     then current # x # xs
     else x # maxCoverageAfterRemovingOne_insert current xs)"

fun maxCoverageAfterRemovingOne_sort ::
    "(nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list" where
  "maxCoverageAfterRemovingOne_sort [] = []"
| "maxCoverageAfterRemovingOne_sort (x # xs) =
    maxCoverageAfterRemovingOne_insert
      x (maxCoverageAfterRemovingOne_sort xs)"

definition maxCoverageAfterRemovingOne_mergeStep ::
    "(nat \<times> nat) list \<Rightarrow>
     (nat \<times> nat) \<Rightarrow>
     (nat \<times> nat) list" where
  "maxCoverageAfterRemovingOne_mergeStep acc current =
    (case acc of
       [] \<Rightarrow> [current]
     | (s, e) # rest \<Rightarrow>
         if fst current \<le> e
         then (s, max e (snd current)) # rest
         else current # acc)"

definition maxCoverageAfterRemovingOne_coverage ::
    "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> nat" where
  "maxCoverageAfterRemovingOne_coverage intervals i =
    (let remaining = maxCoverageAfterRemovingOne_eraseIdx intervals i;
         sorted = maxCoverageAfterRemovingOne_sort remaining;
         merged =
           foldl maxCoverageAfterRemovingOne_mergeStep [] sorted
     in foldl (\<lambda>acc interval.
          acc + (snd interval - fst interval)) 0 (rev merged))"

definition maxCoverageAfterRemovingOne ::
    "(nat \<times> nat) list \<Rightarrow> nat" where
  "maxCoverageAfterRemovingOne intervals =
    (let n = length intervals
     in if n \<le> 1
        then 0
        else foldl
          (\<lambda>acc i.
            max acc (maxCoverageAfterRemovingOne_coverage intervals i))
          0 [0..<n])"

definition maxCoverageAfterRemovingOne_postcond ::
    "(nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "maxCoverageAfterRemovingOne_postcond intervals result \<longleftrightarrow>
    (\<exists>i<length intervals.
      result = maxCoverageAfterRemovingOne_coverage intervals i \<and>
      (\<forall>j<length intervals.
        maxCoverageAfterRemovingOne_coverage intervals i \<ge>
        maxCoverageAfterRemovingOne_coverage intervals j))"

theorem maxCoverageAfterRemovingOne_spec_satisfied:
  assumes "maxCoverageAfterRemovingOne_precond intervals"
  shows
    "maxCoverageAfterRemovingOne_postcond
      intervals (maxCoverageAfterRemovingOne intervals)"
  sorry

end
