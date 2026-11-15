(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_44,
  catalog title "maxSubarraySumDivisibleByK": an executable prefix-sum program
  returns the maximum sum among nonempty contiguous subarrays whose length is
  divisible by an integer parameter, together with its positive-parameter
  precondition and maximality postcondition. This file contains no proof.
*)

theory verina_advanced_44
  imports Main
begin

definition maxSubarraySumDivisibleByK_precond ::
    "int list \<Rightarrow> int \<Rightarrow> bool" where
  "maxSubarraySumDivisibleByK_precond arr k \<longleftrightarrow> k > 0"

fun maxSubarraySumDivisibleByK_prefixSumsAux ::
    "int \<Rightarrow> int list \<Rightarrow> int list" where
  "maxSubarraySumDivisibleByK_prefixSumsAux acc [] = [acc]"
| "maxSubarraySumDivisibleByK_prefixSumsAux acc (x # xs) =
    acc # maxSubarraySumDivisibleByK_prefixSumsAux (acc + x) xs"

definition maxSubarraySumDivisibleByK_prefixSums ::
    "int list \<Rightarrow> int list" where
  "maxSubarraySumDivisibleByK_prefixSums arr =
    maxSubarraySumDivisibleByK_prefixSumsAux 0 arr"

definition maxSubarraySumDivisibleByK_updateBest ::
    "int list \<Rightarrow> nat \<Rightarrow> int option \<Rightarrow> nat \<Rightarrow>
      int option" where
  "maxSubarraySumDivisibleByK_updateBest prefixSums len best start =
    (let endIdx = start + len;
         subarraySum = prefixSums ! endIdx - prefixSums ! start
     in case best of
          None \<Rightarrow> Some subarraySum
        | Some b \<Rightarrow> Some (max b subarraySum))"

definition maxSubarraySumDivisibleByK_processLen ::
    "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow>
      int option \<Rightarrow> nat \<Rightarrow> int option" where
  "maxSubarraySumDivisibleByK_processLen arr prefixSums k best len =
    (if int len mod k = 0 \<and> len > 0
     then
       foldl
         (maxSubarraySumDivisibleByK_updateBest prefixSums len)
         best [0..<(length arr - len + 1)]
     else best)"

definition maxSubarraySumDivisibleByK ::
    "int list \<Rightarrow> int \<Rightarrow> int" where
  "maxSubarraySumDivisibleByK arr k =
    (let n = length arr
     in if n = 0 \<or> k = 0
        then 0
        else
          (let prefixSums =
                 maxSubarraySumDivisibleByK_prefixSums arr;
               result =
                 foldl
                   (maxSubarraySumDivisibleByK_processLen
                     arr prefixSums k)
                   None [0..<n + 1]
           in case result of None \<Rightarrow> 0 | Some s \<Rightarrow> s))"

definition maxSubarraySumDivisibleByK_subarrays ::
    "int list \<Rightarrow> int list list" where
  "maxSubarraySumDivisibleByK_subarrays arr =
    concat
      (map
        (\<lambda>start.
          map
            (\<lambda>len. take len (drop start arr))
            [0..<(length arr - start + 1)])
        [0..<length arr])"

definition maxSubarraySumDivisibleByK_divisibleSubarrays ::
    "int list \<Rightarrow> int \<Rightarrow> int list list" where
  "maxSubarraySumDivisibleByK_divisibleSubarrays arr k =
    filter
      (\<lambda>subarray.
        length subarray mod nat k = 0 \<and> length subarray > 0)
      (maxSubarraySumDivisibleByK_subarrays arr)"

definition maxSubarraySumDivisibleByK_subarraySums ::
    "int list \<Rightarrow> int \<Rightarrow> int list" where
  "maxSubarraySumDivisibleByK_subarraySums arr k =
    map sum_list (maxSubarraySumDivisibleByK_divisibleSubarrays arr k)"

definition maxSubarraySumDivisibleByK_postcond ::
    "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "maxSubarraySumDivisibleByK_postcond arr k result \<longleftrightarrow>
    (let subarraySums =
       maxSubarraySumDivisibleByK_subarraySums arr k
     in
       (length subarraySums = 0 \<longrightarrow> result = 0) \<and>
       (length subarraySums > 0 \<longrightarrow>
         result \<in> set subarraySums \<and>
         list_all (\<lambda>subarraySum. subarraySum \<le> result)
           subarraySums))"

theorem maxSubarraySumDivisibleByK_spec_satisfied:
  "maxSubarraySumDivisibleByK_postcond
    arr k (maxSubarraySumDivisibleByK arr k)"
  sorry

end
