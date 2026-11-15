(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4971339,
  "British flag theorem": in an arbitrary real inner-product affine space, a
  parallelogram with a right angle has equal sums of squared distances from
  any point to its two pairs of opposite vertices. This file contains no proof.
*)

let q4971339_real_inner_product_space = new_definition
  `q4971339_real_inner_product_space
      (z:'v) (addv:'v->'v->'v) (negv:'v->'v)
      (smulv:real->'v->'v) (innerp:'v->'v->real) <=>
     (!x y u:'v. addv (addv x y) u = addv x (addv y u)) /\
     (!x y:'v. addv x y = addv y x) /\
     (!x:'v. addv z x = x) /\
     (!x:'v. addv (negv x) x = z) /\
     (!x:'v. smulv (&1) x = x) /\
     (!r s:real. !x:'v. smulv (r * s) x = smulv r (smulv s x)) /\
     (!r s:real. !x:'v. smulv (r + s) x = addv (smulv r x) (smulv s x)) /\
     (!r:real. !x y:'v. smulv r (addv x y) =
                            addv (smulv r x) (smulv r y)) /\
     (!x y u:'v. innerp (addv x y) u = innerp x u + innerp y u) /\
     (!r:real. !x y:'v. innerp (smulv r x) y = r * innerp x y) /\
     (!x y:'v. innerp x y = innerp y x) /\
     (!x:'v. &0 <= innerp x x) /\
     (!x:'v. innerp x x = &0 <=> x = z)`;;

let Q4971339_BRITISH_FLAG_THEOREM =
  `!(z:'v) addv negv smulv innerp a b c d p.
     q4971339_real_inner_product_space z addv negv smulv innerp /\
     addv a c = addv b d /\
     innerp (addv b (negv a)) (addv d (negv a)) = &0
     ==> innerp (addv p (negv a)) (addv p (negv a)) +
         innerp (addv p (negv c)) (addv p (negv c)) =
         innerp (addv p (negv b)) (addv p (negv b)) +
         innerp (addv p (negv d)) (addv p (negv d))`;;
