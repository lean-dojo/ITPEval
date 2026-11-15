let cring = new_definition
  `cring (zero:'r) (oneR:'r) (add:'r->'r->'r) (mul:'r->'r->'r) (opp:'r->'r) <=>
     (!x y. add x y = add y x) /\
     (!x y z. add (add x y) z = add x (add y z)) /\
     (!x. add x zero = x) /\
     (!x. add x (opp x) = zero) /\
     (!x y. mul x y = mul y x) /\
     (!x y z. mul (mul x y) z = mul x (mul y z)) /\
     (!x. mul x oneR = x) /\
     (!a x y. mul a (add x y) = add (mul a x) (mul a y)) /\
     (!x y. opp (add x y) = add (opp x) (opp y))`;;

let IsIdeal = new_definition
  `IsIdeal (zero:'r) (add:'r->'r->'r) (mul:'r->'r->'r) (opp:'r->'r)
           (ideal:'r->bool) <=>
     ideal zero /\
     (!x y. ideal x /\ ideal y ==> ideal (add x y)) /\
     (!x. ideal x ==> ideal (opp x)) /\
     (!a x. ideal x ==> ideal (mul a x))`;;

let inter = new_definition
  `inter (fam:'i->'r->bool) = (\x:'r. !i. fam i x)`;;

let add_rearrange =
  `!zeroR:'r oneR:'r (add:'r->'r->'r) (mul:'r->'r->'r) (opp:'r->'r).
      cring zeroR oneR add mul opp ==>
      !a:'r b c d. add (add a b) (add c d) = add (add a c) (add b d)`;;

let ideal_sum = new_definition
  `ideal_sum (add:'r->'r->'r) (ideal1:'r->bool) (ideal2:'r->bool) =
     (\x:'r. ?a b. ideal1 a /\ ideal2 b /\ x = add a b)`;;

let inter_isIdeal =
  `!zeroR oneR add mul opp (fam:'i->'r->bool).
      cring zeroR oneR add mul opp ==>
      (!i. IsIdeal zeroR add mul opp (fam i)) ==>
      IsIdeal zeroR add mul opp (inter fam)`;;

let sum_isIdeal =
  `!zeroR oneR add mul opp (ideal1:'r->bool) (ideal2:'r->bool).
      cring zeroR oneR add mul opp ==>
      IsIdeal zeroR add mul opp ideal1 ==>
      IsIdeal zeroR add mul opp ideal2 ==>
      IsIdeal zeroR add mul opp (ideal_sum add ideal1 ideal2)`;;
