(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_22,
  catalog title "isPeakValley": a deterministic scan recognizes integer lists
  that strictly increase and then strictly decrease, together with its total
  correctness contract. This file contains no proof.
*)

let isPeakValley_precond = new_definition
  `isPeakValley_precond (lst:int list) <=> T`;;

let isPeakValley_aux =
  new_recursive_definition list_RECURSION
    `(!increasing:bool. !startedDecreasing:bool.
        isPeakValley_aux increasing startedDecreasing [] =
        (increasing /\ startedDecreasing)) /\
     (!x:int. !rest:int list.
      !increasing:bool. !startedDecreasing:bool.
        isPeakValley_aux increasing startedDecreasing (CONS x rest) =
        if rest = [] then increasing /\ startedDecreasing
        else
          let y = HD rest in
          if x < y then
            if startedDecreasing then F
            else isPeakValley_aux T startedDecreasing rest
          else if x > y then
            if increasing then isPeakValley_aux increasing T rest
            else F
          else F)`;;

let isPeakValley = new_definition
  `isPeakValley (lst:int list) = isPeakValley_aux F F lst`;;

let isPeakValley_range =
  new_recursive_definition num_RECURSION
    `(isPeakValley_range 0 = []) /\
     (!n:num.
        isPeakValley_range (SUC n) =
        APPEND (isPeakValley_range n) (CONS n []))`;;

let isPeakValley_validPeak = new_definition
  `isPeakValley_validPeak (lst:int list) (p:num) <=>
     1 <= p /\
     p < LENGTH lst - 1 /\
     ALL
       (\i:num. EL i lst < EL (i + 1) lst)
       (isPeakValley_range p) /\
     ALL
       (\i:num. EL (p + i) lst > EL (p + i + 1) lst)
       (isPeakValley_range (LENGTH lst - 1 - p))`;;

let isPeakValley_validPeaks = new_definition
  `isPeakValley_validPeaks (lst:int list) =
     FILTER
       (isPeakValley_validPeak lst)
       (isPeakValley_range (LENGTH lst))`;;

let isPeakValley_postcond = new_definition
  `isPeakValley_postcond (lst:int list) (result:bool) <=>
     let validPeaks = isPeakValley_validPeaks lst in
     (~(validPeaks = []) ==> result) /\
     (LENGTH validPeaks = 0 ==> ~result)`;;

let isPeakValley_spec_satisfied =
  `!lst:int list.
     isPeakValley_precond lst
     ==> isPeakValley_postcond lst (isPeakValley lst)`;;
