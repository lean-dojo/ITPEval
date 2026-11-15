let sUnion = new_definition
  `sUnion (A:'a->bool) (B:'a->bool) = \x. A x \/ B x`;;

let sInter = new_definition
  `sInter (A:'a->bool) (B:'a->bool) = \x. A x /\ B x`;;

let sCompl = new_definition
  `sCompl (A:'a->bool) = \x. ~A x`;;

let inter_distrib_left =
  `!A B C x. sInter A (sUnion B C) x <=> sUnion (sInter A B) (sInter A C) x`;;

let inter_distrib_right =
  `!A B C x. sInter (sUnion A B) C x <=> sUnion (sInter A C) (sInter B C) x`;;

let de_morgan_union =
  `!A B x. sCompl (sUnion A B) x <=> sInter (sCompl A) (sCompl B) x`;;

let de_morgan_inter =
  `!A B x. sCompl (sInter A B) x <=> sUnion (sCompl A) (sCompl B) x`;;

