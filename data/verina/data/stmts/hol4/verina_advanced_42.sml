(*
  Statement-only formalization of VERINA artifact verina_advanced_42,
  cataloged as "maxProfit": the executable one-pass program returns the
  maximum natural-number profit from buying on one day and selling on a
  later day, or zero when no profitable transaction exists. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory;

val maxProfit_precond_def = new_definition (
  "maxProfit_precond_def",
  ``maxProfit_precond (prices : num list) <=> T``
);

val updateMinAndProfit_def = new_definition (
  "updateMinAndProfit_def",
  ``updateMinAndProfit
      (price : num) (minSoFar : num) (currentMaxProfit : num) =
      let newMin =
        if minSoFar <= price then minSoFar else price
      in
      let profit =
        if price > minSoFar then price - minSoFar else 0
      in
      let newMaxProfit =
        if currentMaxProfit < profit then profit else currentMaxProfit
      in
        (newMin,newMaxProfit)``
);

val maxProfitAux_def = Define `
  (maxProfitAux
      ([] : num list) (minSoFar : num) (currentMaxProfit : num) =
     currentMaxProfit) /\
  (maxProfitAux
      (price::prices) minSoFar currentMaxProfit =
     let updated =
       updateMinAndProfit price minSoFar currentMaxProfit
     in
       maxProfitAux prices (FST updated) (SND updated))
`;

val maxProfit_def = Define `
  (maxProfit ([] : num list) = 0) /\
  (maxProfit (price::prices) =
     maxProfitAux prices price 0)
`;

val maxProfit_zipIdxFrom_def = Define `
  (maxProfit_zipIdxFrom
      (index : num) ([] : num list) =
     ([] : (num # num) list)) /\
  (maxProfit_zipIdxFrom index (price::prices) =
     (price,index)::maxProfit_zipIdxFrom (SUC index) prices)
`;

val maxProfit_zipIdx_def = new_definition (
  "maxProfit_zipIdx_def",
  ``maxProfit_zipIdx (prices : num list) =
      maxProfit_zipIdxFrom 0 prices``
);

val maxProfit_pairwiseBound_def = Define `
  (maxProfit_pairwiseBound
      ([] : (num # num) list) (result : num) = T) /\
  (maxProfit_pairwiseBound (pricedDay::pricedDays) result =
     (EVERY
        (\laterPricedDay : num # num.
           SND pricedDay < SND laterPricedDay ==>
           FST laterPricedDay - FST pricedDay <= result)
        pricedDays /\
      maxProfit_pairwiseBound pricedDays result))
`;

val maxProfit_postcond_def = new_definition (
  "maxProfit_postcond_def",
  ``maxProfit_postcond
      (prices : num list) (result : num) <=>
      let pricedDays = maxProfit_zipIdx prices
      in
        maxProfit_pairwiseBound pricedDays result /\
        (result = 0 <=>
          LENGTH prices <= 1 \/
          EVERY
            (\pricedDay : num # num.
               EVERY
                 (\otherPricedDay : num # num.
                    SND pricedDay >= SND otherPricedDay \/
                    FST otherPricedDay <= FST pricedDay)
                 pricedDays)
            pricedDays) /\
        (result > 0 ==>
          EXISTS
            (\pricedDay : num # num.
               EXISTS
                 (\laterPricedDay : num # num.
                    SND pricedDay < SND laterPricedDay /\
                    FST laterPricedDay - FST pricedDay = result)
                 pricedDays)
            pricedDays)``
);

val maxProfit_spec_satisfied =
  ``!prices : num list.
      maxProfit_precond prices ==>
      maxProfit_postcond prices (maxProfit prices)``;
