let field_like = new_definition
  `field_like (zero_F:'a) (one_F:'a) (add_F:'a->'a->'a) (mul_F:'a->'a->'a)
              (opp_F:'a->'a) (inv_F:'a->'a) <=>
     (!x:'a y:'a. add_F x y = add_F y x) /\
     (!x:'a y:'a z:'a. add_F (add_F x y) z = add_F x (add_F y z)) /\
     (!x:'a. add_F x zero_F = x) /\
     (!x:'a. add_F (opp_F x) x = zero_F) /\
     (!x:'a y:'a. mul_F x y = mul_F y x) /\
     (!x:'a y:'a z:'a. mul_F (mul_F x y) z = mul_F x (mul_F y z)) /\
     (!x:'a. mul_F one_F x = x) /\
     (!x:'a. ~(x = zero_F) ==> mul_F (inv_F x) x = one_F) /\
     (!x:'a y:'a z:'a. mul_F x (add_F y z) = add_F (mul_F x y) (mul_F x z)) /\
     ~(zero_F = one_F) /\
     (!x:'a. ~(x = zero_F) ==> ~(inv_F x = zero_F))`;;

let tower = new_definition
  `tower (solv:'a->bool) (mp:'a->'a) (splt:'a->bool) <=>
     (!p:'a q:'a. solv p ==> solv (mp q) ==> solv q) /\
     (!p:'a. solv p ==> solv (mp p)) /\
     (!p:'a. splt p ==> solv p)`;;

let zero_add =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==> !x:'f. add_F zero_F x = x`;;

let mul_one_r =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==> !x. mul_F x one_F = x`;;

let mul_inv_r =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x. ~(x = zero_F) ==> mul_F x (inv_F x) = one_F`;;

let add_cancel_l =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. add_F x y = add_F x z ==> y = z`;;

let add_cancel_r =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. add_F y x = add_F z x ==> y = z`;;

let mul_cancel_l =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. ~(x = zero_F) ==> mul_F x y = mul_F x z ==> y = z`;;

let mul_cancel_r =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y z. ~(x = zero_F) ==> mul_F y x = mul_F z x ==> y = z`;;

let inv_unique =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x y. ~(x = zero_F) ==> mul_F x y = one_F ==> y = inv_F x`;;

let inv_involutive =
  `!zero_F:'f one_F:'f (add_F:'f->'f->'f) (mul_F:'f->'f->'f)
      (opp_F:'f->'f) (inv_F:'f->'f).
      field_like zero_F one_F add_F mul_F opp_F inv_F ==>
      !x. ~(x = zero_F) ==> inv_F (inv_F x) = x`;;

let gal_isSolvable_tower =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv q`;;

let gal_isSolvable_double_tower =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a r:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv (mp r) ==> solv r`;;

let gal_isSolvable_triple_tower =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a r:'a s:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv (mp r) ==> solv (mp s) ==> solv s`;;

let gal_isSolvable_quadruple_tower =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a r:'a s:'a t:'a.
      tower solv mp splt ==> solv p ==> solv (mp q) ==> solv (mp r) ==> solv (mp s) ==> solv (mp t) ==> solv t`;;

let gal_isSolvable_map_poly =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp p)`;;

let gal_isSolvable_of_split =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> splt p ==> solv p`;;

let gal_isSolvable_split_tower =
  `!solv:'a->bool mp:'a->'a splt:'a->bool q:'a.
      tower solv mp splt ==> splt q ==> solv q`;;

let gal_isSolvable_two_step_map =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp (mp p))`;;

let gal_isSolvable_three_step_map =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp (mp (mp p)))`;;

let gal_isSolvable_map_poly_comp =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> solv p ==> solv (mp (mp p))`;;

let gal_isSolvable_mutual_split =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a q:'a.
      tower solv mp splt ==> splt p ==> splt q ==> solv p /\ solv q`;;

let gal_isSolvable_map_after_split =
  `!solv:'a->bool mp:'a->'a splt:'a->bool p:'a.
      tower solv mp splt ==> splt p ==> solv (mp p)`;;

let gal_isSolvable_tower_split =
  `!solv:'a->bool mp:'a->'a splt:'a->bool q:'a r:'a.
      tower solv mp splt ==> splt q ==> solv (mp r) ==> solv r`;;
