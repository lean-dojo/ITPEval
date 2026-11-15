(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_42,
  catalog title "maxProfit": an executable natural-number list scan computes
  the greatest profit from buying at an earlier index and selling later, or
  zero when no profitable transaction exists. This file contains no proof.
*)

let maxProfit_precond = new_definition
  `maxProfit_precond (prices:num list) <=> T`;;

let updateMinAndProfit = new_definition
  `updateMinAndProfit
      (price:num) (minSoFar:num) (bestProfit:num) =
     let newMin =
       if minSoFar <= price then minSoFar else price in
     let profit =
       if price > minSoFar then price - minSoFar else 0 in
     let newBestProfit =
       if bestProfit <= profit then profit else bestProfit in
     (newMin,newBestProfit)`;;

let maxProfitAux =
  new_recursive_definition list_RECURSION
    `(!minSoFar:num. !bestProfit:num.
        maxProfitAux ([]:num list) minSoFar bestProfit =
        bestProfit) /\
     (!price:num. !prices:num list.
      !minSoFar:num. !bestProfit:num.
        maxProfitAux (CONS price prices) minSoFar bestProfit =
        let next =
          updateMinAndProfit price minSoFar bestProfit in
        maxProfitAux prices (FST next) (SND next))`;;

let maxProfit = new_definition
  `maxProfit (prices:num list) =
     if prices = [] then 0
     else maxProfitAux (TL prices) (HD prices) 0`;;

let maxProfit_zipIdxFrom =
  new_recursive_definition list_RECURSION
    `(!start:num.
        maxProfit_zipIdxFrom start ([]:num list) = []) /\
     (!price:num. !prices:num list. !start:num.
        maxProfit_zipIdxFrom start (CONS price prices) =
        CONS (price,start)
          (maxProfit_zipIdxFrom (SUC start) prices))`;;

let maxProfit_zipIdx = new_definition
  `maxProfit_zipIdx (prices:num list) =
     maxProfit_zipIdxFrom 0 prices`;;

let maxProfit_pairwiseBound =
  new_recursive_definition list_RECURSION
    `(!result:num.
        maxProfit_pairwiseBound
          ([]:(num#num)list) result <=> T) /\
     (!current:num#num. !rest:(num#num)list. !result:num.
        maxProfit_pairwiseBound (CONS current rest) result <=>
        ALL
          (\later:num#num.
             SND current < SND later
             ==> FST later - FST current <= result)
          rest /\
        maxProfit_pairwiseBound rest result)`;;

let maxProfit_postcond = new_definition
  `maxProfit_postcond (prices:num list) (result:num) <=>
     let indexed = maxProfit_zipIdx prices in
     maxProfit_pairwiseBound indexed result /\
     (result = 0 <=>
       LENGTH prices <= 1 \/
       ALL
         (\earlier:num#num.
            ALL
              (\later:num#num.
                 SND earlier >= SND later \/
                 FST later <= FST earlier)
              indexed)
         indexed) /\
     (result > 0
      ==> EX
            (\earlier:num#num.
               EX
                 (\later:num#num.
                    SND earlier < SND later /\
                    FST later - FST earlier = result)
                 indexed)
            indexed)`;;

let maxProfit_spec_satisfied =
  `!prices:num list.
     maxProfit_precond prices
     ==> maxProfit_postcond prices (maxProfit prices)`;;
