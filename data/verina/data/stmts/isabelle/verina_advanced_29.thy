(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_29,
  catalog title "longestGoodSubarray": a deterministic sliding-window program
  computes the maximum length among contiguous subarrays whose value
  frequencies are at most a positive bound. This file contains no proof.
*)

theory verina_advanced_29
  imports Main
begin

definition longestGoodSubarray_precond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "longestGoodSubarray_precond nums k \<longleftrightarrow> k > 0"

fun longestGoodSubarray_nthDefault ::
    "'a \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'a" where
  "longestGoodSubarray_nthDefault d [] n = d"
| "longestGoodSubarray_nthDefault d (x # xs) 0 = x"
| "longestGoodSubarray_nthDefault d (x # xs) (Suc n) =
    longestGoodSubarray_nthDefault d xs n"

record longestGoodSubarray_state =
  lgs_left :: nat
  lgs_maxLen :: nat
  lgs_freq :: "nat \<Rightarrow> nat"

fun longestGoodSubarray_shrink ::
    "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow>
      longestGoodSubarray_state \<Rightarrow> longestGoodSubarray_state" where
  "longestGoodSubarray_shrink 0 nums k state = state"
| "longestGoodSubarray_shrink (Suc fuel) nums k state =
    (if \<exists>x. lgs_freq state x > k
     then
       (let lnum =
              longestGoodSubarray_nthDefault 0 nums (lgs_left state);
            lcount = lgs_freq state lnum;
            reduced =
              (if lcount = 1
               then (lgs_freq state)(lnum := 0)
               else (lgs_freq state)(lnum := lcount - 1));
            next =
              state\<lparr>
                lgs_left := Suc (lgs_left state),
                lgs_freq := reduced
              \<rparr>
        in longestGoodSubarray_shrink fuel nums k next)
     else state)"

definition longestGoodSubarray_process ::
    "nat list \<Rightarrow> nat \<Rightarrow>
      longestGoodSubarray_state \<Rightarrow> nat \<Rightarrow>
      longestGoodSubarray_state" where
  "longestGoodSubarray_process nums k state right =
    (let num = longestGoodSubarray_nthDefault 0 nums right;
         count = lgs_freq state num;
         increased = (lgs_freq state)(num := count + 1);
         inserted = state\<lparr>lgs_freq := increased\<rparr>;
         shrunk =
           longestGoodSubarray_shrink (length nums) nums k inserted;
         currentLen = right - lgs_left shrunk + 1
     in shrunk\<lparr>
          lgs_maxLen := max (lgs_maxLen shrunk) currentLen
        \<rparr>)"

definition longestGoodSubarray :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "longestGoodSubarray nums k =
    (let initial =
       \<lparr>
         lgs_left = 0,
         lgs_maxLen = 0,
         lgs_freq = (\<lambda>_. 0)
       \<rparr>;
         final =
           foldl
             (longestGoodSubarray_process nums k)
             initial [0..<length nums]
     in lgs_maxLen final)"

definition longestGoodSubarray_subArrays ::
    "nat list \<Rightarrow> nat list list" where
  "longestGoodSubarray_subArrays nums =
    concat
      (map
        (\<lambda>start.
          map
            (\<lambda>len. take len (drop start nums))
            [0..<(length nums - start + 1)])
        [0..<(length nums + 1)])"

definition longestGoodSubarray_subArrayFreqs ::
    "nat list \<Rightarrow> nat list list" where
  "longestGoodSubarray_subArrayFreqs nums =
    map
      (\<lambda>arr. map (\<lambda>x. count_list arr x) arr)
      (longestGoodSubarray_subArrays nums)"

definition longestGoodSubarray_validSubArrays ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat list list" where
  "longestGoodSubarray_validSubArrays nums k =
    filter
      (list_all (\<lambda>x. x \<le> k))
      (longestGoodSubarray_subArrayFreqs nums)"

definition longestGoodSubarray_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "longestGoodSubarray_postcond nums k result \<longleftrightarrow>
    (let validSubArrays = longestGoodSubarray_validSubArrays nums k
     in
       (nums = [] \<and> result = 0) \<or>
       (nums \<noteq> [] \<and>
         list_ex (\<lambda>arr. length arr = result) validSubArrays \<and>
         list_all (\<lambda>arr. length arr \<le> result) validSubArrays))"

theorem longestGoodSubarray_spec_satisfied:
  assumes "longestGoodSubarray_precond nums k"
  shows
    "longestGoodSubarray_postcond
      nums k (longestGoodSubarray nums k)"
  sorry

end
