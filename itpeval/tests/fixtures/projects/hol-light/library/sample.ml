needs "base.ml";;
let before_arithmetic = base_refl;;

needs "arithmetic.ml";;

let itpeval_neg_def = new_definition
  `itpeval_neg (p:bool) = ~p`;;

let under_assumption = ASSUME `p:bool`;;

let discharge_assumption = DISCH `p:bool` under_assumption;;
