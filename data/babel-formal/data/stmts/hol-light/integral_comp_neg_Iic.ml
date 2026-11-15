let is_integral_context = new_definition
  `is_integral_context (zero:R) (oneR:R)
                       (add:R->R->R) (opp:R->R) (mul:R->R->R)
                       (le:R->R->bool) (lt:R->R->bool) (absR:R->R)
                       (sigma:(R->bool)->(R->R)->R) <=>
     (!x:R y:R. add x y = add y x) /\
     (!x:R y:R z:R. add (add x y) z = add x (add y z)) /\
     (!x:R. add x zero = x) /\
     (!x:R. add (opp x) x = zero) /\
     (!x:R y:R z:R. add x z = add y z ==> x = y) /\
     (!x:R y:R. mul x y = mul y x) /\
     (!x:R y:R z:R. mul (mul x y) z = mul x (mul y z)) /\
     (!x:R. mul x oneR = x) /\
     (!x:R y:R z:R. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x:R. opp (opp x) = x) /\
     (!x:R y:R z:R. le x y ==> le (add x z) (add y z)) /\
     (!x:R y:R z:R. le zero z ==> le x y ==> le (mul x z) (mul y z)) /\
     le zero oneR /\
     (!x:R y:R. le x y \/ le y x) /\
     (!x:R y:R. le x y \/ ~(le x y)) /\
     (!x:R y:R. le x y ==> le (opp y) (opp x)) /\
     (!x:R y:R. le x y ==> le y x ==> x = y) /\
     (!x:R y:R. lt x y ==> lt (opp y) (opp x)) /\
     (!x:R. le x x) /\
     (!x:R y:R z:R. le x y ==> le y z ==> le x z) /\
     (!x:R y:R. lt x y <=> (le x y /\ ~(x = y))) /\
     (!x:R. le zero x ==> absR x = x) /\
     (!x:R. le x zero ==> absR x = opp x) /\
     (!x:R. le zero (absR x)) /\
     (!x:R. absR (opp x) = absR x) /\
     (!x:R y:R. le (absR (add x y)) (add (absR x) (absR y))) /\
     (!D:R->bool f:R->R c:R. sigma D (\x. mul c (f x)) = mul c (sigma D f)) /\
     (!D:R->bool f:R->R g:R->R. (!x:R. D x ==> f x = g x) ==> sigma D f = sigma D g) /\
     (!D:R->bool. sigma D (\x:R. zero) = zero) /\
     (!D:R->bool f:R->R g:R->R. sigma D (\x. add (f x) (g x)) = add (sigma D f) (sigma D g)) /\
     (!D:R->bool E:R->bool f:R->R. (!x:R. D x ==> E x ==> F) ==> sigma (\x. D x \/ E x) f = add (sigma D f) (sigma E f)) /\
     (!D:R->bool f:R->R g:R->R. (!x:R. D x ==> le (f x) (g x)) ==> le (sigma D f) (sigma D g)) /\
     (!D:R->bool E:R->bool f:R->R. (!x:R. D x <=> E x) ==> sigma D f = sigma E f)`;;

let iic = new_definition `iic (le:R->R->bool) c x <=> le x c`;;
let ioi = new_definition `ioi (lt:R->R->bool) c x <=> lt c x`;;
let iio = new_definition `iio (lt:R->R->bool) c x <=> lt x c`;;

let unionD = new_definition `unionD (D:R->bool) (E:R->bool) x <=> D x \/ E x`;;
let interD = new_definition `interD (D:R->bool) (E:R->bool) x <=> D x /\ E x`;;

let preimage = new_definition `preimage (g:R->R) (D:R->bool) x <=> D (g x)`;;

let INTRO_INT_HYPS =
  REWRITE_TAC[is_integral_context] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (fun th -> ASSUME_TAC th THEN MAP_EVERY ASSUME_TAC (CONJUNCTS th));;

let ASSUM_MATCH_TAC pat ttac =
  ASSUM_LIST
    (fun asms ->
      let th =
        find
          (fun th ->
            try
              let (_,tinst,_) = term_match [] pat (concl th) in
              forall (fun (v,t) -> t = v) tinst
            with Failure _ -> false)
          asms in
      ttac th);;

let INT_CONTEXT_CONJ n ctx =
  List.nth (CONJUNCTS (REWRITE_RULE[is_integral_context] ctx)) n;;

let lt_irrefl =
  `!zero oneR add opp mul le lt absR sigma x.
     is_integral_context zero oneR add opp mul le lt absR sigma ==> ~(lt x x)`;;

let lt_trans_strict =
  `!zero oneR add opp mul le lt absR sigma x y z.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> lt x y ==> lt y z ==> lt x z`;;

let preimage_union =
  `!D E (g:R->R) x.
     preimage g (unionD D E) x <=> preimage g D x \/ preimage g E x`;;

let preimage_inter =
  `!D E (g:R->R) x.
     preimage g (interD D E) x <=> preimage g D x /\ preimage g E x`;;

let preimage_neg_Ioi =
  `!zero oneR add opp mul le lt absR sigma c x.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (preimage opp (ioi lt c) x <=> lt x (opp c))`;;

let preimage_neg_Iic =
  `!zero oneR add opp mul le lt absR sigma c x.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (preimage opp (iic le c) x <=> iic le x (opp c))`;;

let preimage_comp =
  `!D (g:R->R) (h:R->R) x.
     preimage g (preimage h D) x <=> preimage (\x. h (g x)) D x`;;

let integral_neg =
  `!(zero:R) (oneR:R) (add:R->R->R) (opp:R->R) (mul:R->R->R)
      (le:R->R->bool) (lt:R->R->bool) (absR:R->R)
      (sigma:(R->bool)->(R->R)->R) (D:R->bool) (phi:R->R).
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma D (\x. opp (phi x)) = opp (sigma D phi)`;;

let integral_sub =
  `!zero oneR add opp mul le lt absR sigma D f g.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma D (\x. add (f x) (opp (g x))) = add (sigma D f) (opp (sigma D g))`;;

let sigma_empty =
  `!zero oneR add opp mul le lt absR sigma f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma (\x. F) f = zero`;;

let sigma_bilinear =
  `!zero oneR add opp mul le lt absR sigma D f g c d.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma D (\x. add (mul c (f x)) (mul d (g x))) =
         add (mul c (sigma D f)) (mul d (sigma D g))`;;

let sigma_le_monotone =
  `!zero oneR add opp mul le lt absR sigma D f g.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (!x. D x ==> le (f x) (g x)) ==> le (sigma D f) (sigma D g)`;;

let sigma_nonneg =
  `!zero oneR add opp mul le lt absR sigma D f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (!x. D x ==> le zero (f x)) ==> le zero (sigma D f)`;;

let sigma_split =
  `!zero oneR add opp mul le lt absR sigma D P f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> (!x. D x ==> P x \/ ~(P x))
     ==> sigma D f =
         add (sigma (\x. D x /\ P x) f) (sigma (\x. D x /\ ~(P x)) f)`;;

let sigma_preimage_neg_Ioi =
  `!zero oneR add opp mul le lt absR sigma f c.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> sigma (preimage opp (ioi lt c)) f = sigma (iio lt (opp c)) f`;;

let sigma_abs_bound =
  `!zero oneR add opp mul le lt absR sigma D f.
     is_integral_context zero oneR add opp mul le lt absR sigma
     ==> le (absR (sigma D f)) (sigma D (\x. absR (f x)))`;;
