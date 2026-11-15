let is_supinf_context = new_definition
  `is_supinf_context (zero_nat:N) (Succ:N->N)
		                     (NatAltle:N->N->bool)
		                     (zero:R) (oneR:R) (add:R->R->R) (mul:R->R->R)
		                     (opp:R->R) (invR:R->R)
		                     (Rle:R->R->bool) (Rlt:R->R->bool) (Rabs:R->R)
		                     (ofNat:N->R) <=>
	     (!n. NatAltle n n) /\
	     (!n m. NatAltle n m ==> NatAltle n (Succ m)) /\
	     (!n. NatAltle n (Succ n)) /\
	     (!x y. add x y = add y x) /\
	     (!x y z. add (add x y) z = add x (add y z)) /\
	     (!x. add x zero = x) /\
	     (!x. add (opp x) x = zero) /\
	     (!x y. mul x y = mul y x) /\
	     (!x y z. mul (mul x y) z = mul x (mul y z)) /\
	     (!x. mul x oneR = x) /\
     (!x y z. mul x (add y z) = add (mul x y) (mul x z)) /\
     (!x. add x (opp zero) = x) /\
     (!x. Rle x x) /\
     (!x y z. Rle x y /\ Rle y z ==> Rle x z) /\
     (!x y. Rle x y /\ Rle y x ==> x = y) /\
     (!x y. Rlt x y <=> (Rle x y /\ ~(x = y))) /\
     (!x. Rle (add x (opp zero)) (Rabs x)) /\
     (!x. Rlt zero x ==> Rlt zero (invR x)) /\
     (!x y z. Rle y z ==> Rle (add x y) (add x z)) /\
     (!x. Rlt zero x ==> invR (invR x) = x) /\
	     (!n. Rlt zero (ofNat (Succ n))) /\
	     (!m n. NatAltle m n ==> Rle (ofNat m) (ofNat n)) /\
	     (ofNat zero_nat = zero) /\
	     (!n. ofNat (Succ n) = add (ofNat n) oneR) /\
	     (!x y. Rlt x y \/ x = y \/ Rlt y x) /\
	     (!a b. Rlt zero a /\ Rlt zero b /\ Rle a b ==> Rle (invR b) (invR a)) /\
	     (!x y. Rlt x y ==> ?eps. Rlt zero eps /\ Rlt (add x eps) y) /\
		     (!x. ?n. Rle x (ofNat n)) /\
		     (!A. (?ub. !a. A a ==> Rle ub a) ==>
		          ?sup. (!a. A a ==> Rle a sup) /\
		                (!y. (!a. A a ==> Rle a y) ==> Rle sup y))`;;

let sub = new_definition
  `sub (add:R->R->R) (opp:R->R) x y = add x (opp y)`;;

let up_bounds = new_definition
  `up_bounds (Rle:R->R->bool) (A:R->bool) x <=>
     !a. A a ==> Rle a x`;;

let is_maximum = new_definition
  `is_maximum (Rle:R->R->bool) (A:R->bool) x <=>
     A x /\ up_bounds Rle A x`;;

let low_bounds = new_definition
  `low_bounds (Rle:R->R->bool) (A:R->bool) x <=>
     !a. A a ==> Rle x a`;;

let is_inf = new_definition
  `is_inf (Rle:R->R->bool) (A:R->bool) x <=>
     is_maximum Rle (low_bounds Rle A) x`;;

let limit = new_definition
  `limit (zero:R) (Rlt:R->R->bool) (Rabs:R->R) (Rle:R->R->bool)
         (subf:R->R->R) (NatAltle:N->N->bool) u l <=>
     !eps. Rlt zero eps ==> ?N. !n. NatAltle N n ==> Rle (Rabs (subf (u n) l)) eps`;;

let INTRO_SUPINF_HYPS =
  REWRITE_TAC[is_supinf_context] THEN REPEAT GEN_TAC THEN
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

let supinf_order_core =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat.
     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
     ==> (!x. Rle x x) /\
         (!x y z. Rle x y /\ Rle y z ==> Rle x z) /\
         (!x y. Rle x y /\ Rle y x ==> x = y) /\
         (!x y. Rlt x y <=> Rle x y /\ ~(x = y)) /\
         (!x y. Rlt x y \/ x = y \/ Rlt y x) /\
         (!x y. Rlt x y ==> ?eps. Rlt zero eps /\ Rlt (add x eps) y)`;;

let inf_lt_core =
  `!Rle Rlt (A:R->bool) x y.
     (!x. Rle x x) /\
     (!x y. Rle x y /\ Rle y x ==> x = y) /\
     (!x y. Rlt x y <=> Rle x y /\ ~(x = y)) /\
     (!x y. Rlt x y \/ x = y \/ Rlt y x)
     ==> is_inf Rle A x ==> Rlt x y ==> ?a. A a /\ Rlt a y`;;

let not_lt_of_le_core =
  `!Rle Rlt (x:A) y.
     (!u v. Rle u v /\ Rle v u ==> u = v) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v))
     ==> Rlt x y ==> ~(Rle y x)`;;

let lt_of_not_le_core =
  `!Rle Rlt (x:A) y.
     (!u. Rle u u) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v)) /\
     (!u v. Rlt u v \/ u = v \/ Rlt v u)
     ==> ~(Rle y x) ==> Rlt x y`;;

let le_of_le_add_eps_core =
  `!zero (add:A->A->A) Rle Rlt x y.
     (!u. Rle u u) /\
     (!u v. Rle u v /\ Rle v u ==> u = v) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v)) /\
     (!u v. Rlt u v \/ u = v \/ Rlt v u) /\
     (!u v. Rlt u v ==> ?eps. Rlt zero eps /\ Rlt (add u eps) v)
     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
     ==> Rle y x`;;

let le_of_le_add_eps_r_core =
  `!(zero:R) (add:R->R->R) Rle Rlt x y.
     (!u. Rle u u) /\
     (!u v. Rle u v /\ Rle v u ==> u = v) /\
     (!u v. Rlt u v <=> Rle u v /\ ~(u = v)) /\
     (!u v. Rlt u v \/ u = v \/ Rlt v u) /\
     (!u v. Rlt u v ==> ?eps. Rlt zero eps /\ Rlt (add u eps) v)
     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
     ==> Rle y x`;;

let le_of_le_add_eps_r_core_imp =
  `!(zero:R) (add:R->R->R) Rle Rlt x y.
     (!u. Rle u u)
     ==> (!u v. Rle u v /\ Rle v u ==> u = v)
     ==> (!u v. Rlt u v <=> Rle u v /\ ~(u = v))
     ==> (!u v. Rlt u v \/ u = v \/ Rlt v u)
     ==> (!u v. Rlt u v ==> ?eps. Rlt zero eps /\ Rlt (add u eps) v)
     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
     ==> Rle y x`;;

let add_sub_cancel_r =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat a b.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> add a (sub add opp b a) = b`;;

let rabs_pos =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat t.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> Rle t (Rabs t)`;;

let unique_max =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat (A:R->bool) x y.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> is_maximum Rle A x ==> is_maximum Rle A y ==> x = y`;;

let inf_lt =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat (A:R->bool) x y.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> is_inf Rle A x ==> Rlt x y ==> ?a. A a /\ Rlt a y`;;

let le_of_le_add_eps =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat x y.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> (!eps. Rlt zero eps ==> Rle y (add x eps))
	     ==> Rle y x`;;

let le_lim_eps_core =
  `!(zero:R) (add:R->R->R) Rle Rlt Rabs subf NatAltle (u:N->R) x y eps.
     (!n. NatAltle n n) /\
     (!a b c. Rle a b /\ Rle b c ==> Rle a c) /\
     (!a b c. Rle b c ==> Rle (add a b) (add a c)) /\
     (!t. Rle t (Rabs t)) /\
     (!a b. add a (subf b a) = b) /\
     (!eps. Rlt zero eps ==> ?N. !n. NatAltle N n ==> Rle (Rabs (subf (u n) x)) eps) /\
     (!n. Rle y (u n)) /\
     Rlt zero eps
     ==> Rle y (add x eps)`;;

let le_lim_eps_core_imp =
  `!(zero:R) (add:R->R->R) Rle Rlt Rabs subf NatAltle (u:N->R) x y eps.
     (!n. NatAltle n n)
     ==> (!a b c. Rle a b /\ Rle b c ==> Rle a c)
     ==> (!a b c. Rle b c ==> Rle (add a b) (add a c))
     ==> (!t. Rle t (Rabs t))
     ==> (!a b. add a (subf b a) = b)
     ==> (!eps. Rlt zero eps ==> ?N. !n. NatAltle N n ==> Rle (Rabs (subf (u n) x)) eps)
     ==> (!n. Rle y (u n))
     ==> Rlt zero eps
     ==> Rle y (add x eps)`;;

let le_lim_core =
  `!(zero:R) (add:R->R->R) Rle Rlt Rabs subf NatAltle (u:N->R) x y.
     (!n. NatAltle n n) /\
     (!a. Rle a a) /\
     (!a b c. Rle a b /\ Rle b c ==> Rle a c) /\
     (!a b. Rle a b /\ Rle b a ==> a = b) /\
     (!a b. Rlt a b <=> Rle a b /\ ~(a = b)) /\
     (!a b. Rlt a b \/ a = b \/ Rlt b a) /\
     (!a b c. Rle b c ==> Rle (add a b) (add a c)) /\
     (!a b. Rlt a b ==> ?eps. Rlt zero eps /\ Rlt (add a eps) b) /\
     (!t. Rle t (Rabs t)) /\
     (!a b. add a (subf b a) = b)
     ==> limit zero Rlt Rabs Rle subf NatAltle u x
     ==> (!n. Rle y (u n))
     ==> Rle y x`;;

let le_lim =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat (u:N->R) x y.
		     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
		     ==> limit zero Rlt Rabs Rle (sub add opp) NatAltle u x
		     ==> (!n. Rle y (u n))
		     ==> Rle y x`;;

let inv_succ_pos =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat n.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> Rlt zero (invR (ofNat (Succ n)))`;;

let limit_inv_succ =
  `!zero_nat Succ NatAltle (zero:R) oneR add mul opp invR Rle Rlt Rabs ofNat eps.
	     is_supinf_context zero_nat Succ NatAltle zero oneR add mul opp invR Rle Rlt Rabs ofNat
	     ==> Rlt zero eps
	     ==> ?N. !n. NatAltle N n ==> Rle (invR (ofNat (Succ n))) eps`;;
