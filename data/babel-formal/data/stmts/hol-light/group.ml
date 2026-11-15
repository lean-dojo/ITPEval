let is_group = new_definition
  `is_group (mul:A->A->A) (e:A) (ginv:A->A) <=>
     (!a b c. mul a (mul b c) = mul (mul a b) c) /\
     (!a. mul a e = a) /\
     (!a. mul e a = a) /\
     (!a. mul (ginv a) a = e) /\
     (!a. mul a (ginv a) = e)`;;


let INTRO_GROUP_HYPS =
  REWRITE_TAC[is_group] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))));;



let FUN_CONG =
  `!f:A->B x y. x = y ==> f x = f y`;;

let GROUP_ASSOC =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b c:A. mul a (mul b c) = mul (mul a b) c`;;

let GROUP_ASSOC_SYM =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b c:A. mul (mul a b) c = mul a (mul b c)`;;

let GROUP_MUL_ONE =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul a e = a`;;

let GROUP_ONE_MUL =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul e a = a`;;

let GROUP_MUL_INV_L =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul (ginv a) a = e`;;

let GROUP_MUL_INV_R =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a:A. mul a (ginv a) = e`;;

let GROUP_LEFT_CANCEL_NORMALIZE =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b:A. mul (ginv a) (mul a b) = b`;;

let GROUP_RIGHT_CANCEL_NORMALIZE =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv ==> !a b:A. mul (mul b a) (ginv a) = b`;;

let MUL_LEFT_CANCEL =
  `!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b c:A. mul a b = mul a c ==> b = c`;;

let MUL_RIGHT_CANCEL =
  `!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b c:A. mul b a = mul c a ==> b = c`;;

let INV_INV =
  `!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==> !a:A. ginv (ginv a) = a`;;

let GROUP_INV_MUL_PRODUCT =
  `!mul:A->A->A (e:A) (ginv:A->A).
        is_group mul e ginv
        ==> !a b:A. mul (mul (ginv b) (ginv a)) (mul a b) = e`;;

let INV_MUL =
  `!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b:A. ginv (mul a b) = mul (ginv b) (ginv a)`;;

let INV_EQ_OF_MUL_EQ_ONE =
  `!mul:A->A->A (e:A) (ginv:A->A). is_group mul e ginv ==>
    !a b:A. mul a b = e ==> b = ginv a`;;




let is_group_comm = new_definition
  `is_group_comm (mul:A->A->A) (e:A) (ginv:A->A) <=>
     is_group mul e ginv /\ (!a b. mul a b = mul b a)`;;

let MUL_ROTATE' =
  `!mul (e:A) ginv. is_group_comm mul e ginv ==>
    !a b c. mul a (mul b c) = mul b (mul c a)`;;




let is_group_action = new_definition
  `is_group_action (mul:A->A->A) (e:A) (ginv:A->A) (act:A->B->B) <=>
     is_group mul e ginv /\
     (!x. act e x = x) /\
     (!(g:A) (h:A) (x:B). act (mul g h) x = act g (act h x))`;;

let INTRO_ACTION_HYPS =
  REWRITE_TAC[is_group_action] THEN REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC));;

let GROUP_ACTION_REFL_TAC () =
  ASM_REWRITE_TAC[is_group_action] THEN REFL_TAC;;

let ACT_INV =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !g x. act (ginv g) (act g x) = x`;;

let ACT_INV_SPEC =
  `!mul (e:A) ginv (act:A->B->B) g x. is_group_action mul e ginv act ==>
    act (ginv g) (act g x) = x`;;

let ACT_INV_R =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !g x. act g (act (ginv g) x) = x`;;

let ACT_INV_R_SPEC =
  `!mul (e:A) ginv (act:A->B->B) g x. is_group_action mul e ginv act ==>
    act g (act (ginv g) x) = x`;;

let ACT_INV_R_SYM =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !g x. x = act g (act (ginv g) x)`;;



let is_orbit = new_definition
  `is_orbit (act:A->B->B) x y <=> ?g. act g x = y`;;

let is_stabilizer = new_definition
  `is_stabilizer (act:A->B->B) x g <=> act g x = x`;;

let ORBIT_REFL =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x. is_orbit act x x`;;

let ORBIT_SYM =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y. is_orbit act x y ==> is_orbit act y x`;;

let ORBIT_TRANS =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y z. is_orbit act x y ==> is_orbit act y z ==> is_orbit act x z`;;

let ORBIT_PARTITION =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y z. is_orbit act x y ==>
            (is_orbit act x z <=> is_orbit act y z)`;;

let STABILIZER_MUL =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x g h. is_stabilizer act x g ==> is_stabilizer act x h ==>
            is_stabilizer act x (mul g h)`;;

let STABILIZER_INV =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x g. is_stabilizer act x g ==> is_stabilizer act x (ginv g)`;;

let STABILIZER_ONE =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x. is_stabilizer act x e`;;

let STABILIZER_CONJUGATE =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x g h. is_stabilizer act x h ==>
            is_stabilizer act (act g x) (mul (mul g h) (ginv g))`;;

let CONJUGATE_MUL_CANCEL_LEFT =
  `!mul:A->A->A (e:A) (ginv:A->A) g h.
        is_group mul e ginv
        ==> mul g (mul (mul (ginv g) h) g) = mul h g`;;

let CONJUGATE_MUL_CANCEL =
  `!mul:A->A->A (e:A) (ginv:A->A) g h.
        is_group mul e ginv
        ==> mul (mul g (mul (mul (ginv g) h) g)) (ginv g) = h`;;

let STABILIZER_CONJUGATE_ORBIT_FWD =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y g h. act g x = y ==>
            is_stabilizer act y h ==>
            is_stabilizer act x (mul (mul (ginv g) h) g)`;;

let STABILIZER_CONJUGATE_ORBIT_REV =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y g h. act g x = y ==>
            is_stabilizer act x (mul (mul (ginv g) h) g) ==>
            is_stabilizer act y h`;;
let STABILIZER_CONJUGATE_ORBIT =
  `!mul (e:A) ginv (act:A->B->B). is_group_action mul e ginv act ==>
    !x y g h. act g x = y ==>
            (is_stabilizer act y h <=>
             is_stabilizer act x (mul (mul (ginv g) h) g))`;;
