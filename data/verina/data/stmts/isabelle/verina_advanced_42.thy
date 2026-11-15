(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_42,
  catalog title "maxProfit": an executable natural-number list scan computes
  the maximum profit from buying at an earlier index and selling later,
  together with its precondition and full correctness contract. This file
  contains no proof.
*)

theory verina_advanced_42
  imports Main
begin

definition maxProfit_precond :: "nat list \<Rightarrow> bool" where
  "maxProfit_precond prices \<longleftrightarrow> True"

definition updateMinAndProfit ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  "updateMinAndProfit price minSoFar currentMaxProfit =
    (let newMin = min minSoFar price;
         profit = (if price > minSoFar then price - minSoFar else 0);
         newMaxProfit = max currentMaxProfit profit
     in (newMin, newMaxProfit))"

fun maxProfitAux :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "maxProfitAux [] minSoFar currentMaxProfit = currentMaxProfit"
| "maxProfitAux (p # ps) minSoFar currentMaxProfit =
    (case updateMinAndProfit p minSoFar currentMaxProfit of
       (newMin, newProfit) \<Rightarrow> maxProfitAux ps newMin newProfit)"

definition maxProfit :: "nat list \<Rightarrow> nat" where
  "maxProfit prices =
    (case prices of
       [] \<Rightarrow> 0
     | p # ps \<Rightarrow> maxProfitAux ps p 0)"

definition maxProfit_zipIdx :: "nat list \<Rightarrow> (nat \<times> nat) list" where
  "maxProfit_zipIdx prices = zip prices [0..<length prices]"

fun maxProfit_pairwise ::
    "((nat \<times> nat) \<Rightarrow> (nat \<times> nat) \<Rightarrow> bool) \<Rightarrow>
      (nat \<times> nat) list \<Rightarrow> bool" where
  "maxProfit_pairwise relation [] = True"
| "maxProfit_pairwise relation (x # xs) =
    (list_all (\<lambda>y. relation x y) xs \<and>
     maxProfit_pairwise relation xs)"

definition maxProfit_postcond ::
    "nat list \<Rightarrow> nat \<Rightarrow> bool" where
  "maxProfit_postcond prices result \<longleftrightarrow>
    (let indexedPrices = maxProfit_zipIdx prices
     in
       maxProfit_pairwise
         (\<lambda>x y.
           snd x < snd y \<longrightarrow> fst y - fst x \<le> result)
         indexedPrices \<and>
       (result = 0 \<longleftrightarrow>
         (length prices \<le> 1 \<or>
          list_all
            (\<lambda>x.
              list_all
                (\<lambda>y. snd x \<ge> snd y \<or> fst y \<le> fst x)
                indexedPrices)
            indexedPrices)) \<and>
       (result > 0 \<longrightarrow>
         list_ex
           (\<lambda>x.
             list_ex
               (\<lambda>y.
                 snd x < snd y \<and> fst y - fst x = result)
               indexedPrices)
           indexedPrices))"

theorem maxProfit_spec_satisfied:
  assumes "maxProfit_precond prices"
  shows "maxProfit_postcond prices (maxProfit prices)"
  sorry

end
