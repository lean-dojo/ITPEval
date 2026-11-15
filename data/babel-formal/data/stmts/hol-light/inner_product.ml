let is_inner_context = new_definition
  `is_inner_context (zeroR:R) (oneR:R)
                    (add:R->R->R) (mul:R->R->R) (opp:R->R)
                    (addV:V->V->V) (oppV:V->V) (smul:R->V->V)
                    (ip:V->V->R) <=>
     (!x y. add x y = add y x) /\
     (!x y z. add (add x y) z = add x (add y z)) /\
     (!x. add x zeroR = x) /\
     (!x. add zeroR x = x) /\
     (!x. opp (opp x) = x) /\
     (!x. mul (opp oneR) x = opp x) /\
     (!u. oppV u = smul (opp oneR) u) /\
     (!u v w. ip (addV u v) w = add (ip u w) (ip v w)) /\
     (!a u v. ip (smul a u) v = mul a (ip u v)) /\
     (!u v w. ip u (addV v w) = add (ip u v) (ip u w)) /\
     (!a u v. ip u (smul a v) = mul a (ip u v)) /\
     (!u v. ip u v = ip v u)`;;

let subV = new_definition
  `subV (addV:V->V->V) (oppV:V->V) u v = addV u (oppV v)`;;

let INTRO_INNER_HYPS =
  REWRITE_TAC[is_inner_context] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> ASSUME_TAC th THEN MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

let ip_neg_left =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> ip (oppV u) v = opp (ip u v)`;;

let ip_neg_right =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> ip u (oppV v) = opp (ip u v)`;;

let ip_add_add =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> ip (addV u v) (addV u v) =
         add (add (ip u u) (ip v u)) (add (ip u v) (ip v v))`;;

let opp_opp_ctx =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip x.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> opp (opp x) = x`;;

let add_zero_right_ctx =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip x.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> add x zeroR = x`;;

let add_zero_left_ctx =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip x.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> add zeroR x = x`;;

let ip_symm_ctx =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> ip u v = ip v u`;;

let ip_sub_sub =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> ip (subV addV oppV u v) (subV addV oppV u v) =
         add (add (ip u u) (opp (ip v u))) (add (opp (ip u v)) (ip v v))`;;

let pythagoras =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> ip u v = zeroR
     ==> ip (addV u v) (addV u v) = add (ip u u) (ip v v)`;;

let parallelogram =
  `!zeroR oneR add mul opp (addV:V->V->V) oppV smul ip u v.
     is_inner_context zeroR oneR add mul opp addV oppV smul ip
     ==> add (ip (addV u v) (addV u v))
              (ip (subV addV oppV u v) (subV addV oppV u v)) =
         add (add (add (ip u u) (ip v u)) (add (ip u v) (ip v v)))
             (add (add (ip u u) (opp (ip v u))) (add (opp (ip u v)) (ip v v)))`;;
