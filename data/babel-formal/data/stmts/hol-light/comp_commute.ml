let myComp = new_definition
  `myComp (g:B->C) (f:A->B) = (\x:A. g (f x))`;;

let myId = new_definition
  `myId = (\x:A. x)`;;

let comp_assoc =
  `!h g f. myComp h (myComp g f) = myComp (myComp h g) f`;;

let comp_id_l =
  `!f:A->B. myComp myId f = f`;;

let comp_id_r =
  `!f:A->B. myComp f myId = f`;;

let commute = new_definition
  `commute (f:A->A) (g:A->A) <=> myComp f g = myComp g f`;;

let commute_symm =
  `!f g. commute f g ==> commute g f`;;

let commute_with_id_l =
  `!f:A->A. commute f myId`;;

let commute_with_id_r =
  `!f:A->A. commute myId f`;;

let commute_refl =
  `!f:A->A. commute f f`;;

let commute_congr =
  `!f1 f2 g1 g2:A->A.
      f1 = f2 ==> g1 = g2 ==> commute f1 g1 ==> commute f2 g2`;;

let commute_transport_left_id =
  `!f g:A->A. commute f g ==> commute (myComp myId f) g`;;

let commute_transport_right_id =
  `!f g:A->A. commute f g ==> commute f (myComp myId g)`;;
