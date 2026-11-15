let is_add_monoid = new_definition
  `is_add_monoid (zero:A) (add:A->A->A) <=>
      (!x. add x zero = x) /\
      (!x y. add x y = add y x) /\
      (!x y z. add (add x y) z = add x (add y z))`;;

let is_integral = new_definition
  `is_integral (integral:(A->A)->A) (add:A->A->A) (zero:A) <=>
      (!g h. (!t. g t = h t) ==> integral g = integral h) /\
      (!c. integral (\t. c) = c) /\
      (!f g. integral (\t. add (f t) (g t)) =
             add (integral f) (integral g)) /\
      (!f c. integral (\t. f (add t c)) = integral f)`;;

let circleMap = new_definition
  `circleMap (add:A->A->A) c t = add t c`;;

let circleAverage = new_definition
  `circleAverage (integral:(A->A)->A) (add:A->A->A) (f:A->A) c =
      integral (\t. f (circleMap add c t))`;;

let dest_add_monoid th = CONJUNCTS (REWRITE_RULE[is_add_monoid] th);;
let dest_integral th = CONJUNCTS (REWRITE_RULE[is_integral] th);;

let circleMap_zero =
  `!(zero:A) (add:A->A->A).
      is_add_monoid zero add ==> !t:A. circleMap add zero t = t`;;

let circleAverage_zero =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !f:A->A. circleAverage integral add f zero = integral f`;;

let circleAverage_add =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (g:A->A) (c:A).
        circleAverage integral add (\z. add (f z) (g z)) c =
        add (circleAverage integral add f c) (circleAverage integral add g c)`;;

let circleAverage_fun_add =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f:A->A) (c:A).
        circleAverage integral add (\z. f (add z c)) zero =
        circleAverage integral add f c`;;

let circleMap_add =
  `!(zero:A) (add:A->A->A).
      is_add_monoid zero add ==>
      !(c:A) (d:A) (t:A).
        circleMap add (add c d) t = circleMap add c (circleMap add d t)`;;

let circleAverage_shift =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f:A->A) (c:A) (d:A).
        circleAverage integral add f (add c d) =
        circleAverage integral add (\z. f (add z d)) c`;;

let circleAverage_const =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(k:A) (c:A). circleAverage integral add (\z. k) c = k`;;

let circleAverage_add_const =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (k:A) (c:A).
        circleAverage integral add (\z. add (f z) k) c =
        add (circleAverage integral add f c) k`;;

let circleAverage_comm_add =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f:A->A) (g:A->A) (c:A).
        circleAverage integral add (\z. add (f z) (g z)) c =
        circleAverage integral add (\z. add (g z) (f z)) c`;;

let circleAverage_add_assoc =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f:A->A) (g:A->A) (h:A->A) (c:A).
        circleAverage integral add (\z. add (add (f z) (g z)) (h z)) c =
        add (circleAverage integral add f c)
            (add (circleAverage integral add g c)
                 (circleAverage integral add h c))`;;

let circleAverage_center_comm =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f:A->A) (c:A) (d:A).
        circleAverage integral add f (add c d) =
        circleAverage integral add f (add d c)`;;

let circleAverage_center_independent =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (c:A). circleAverage integral add f c = integral f`;;

let circleAverage_center_eq =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (c:A) (d:A).
        circleAverage integral add f c = circleAverage integral add f d`;;

let circleAverage_idempotent =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (c:A).
        circleAverage integral add (\z. circleAverage integral add f z) c =
        circleAverage integral add f c`;;

let circleAverage_of_zero_integral =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (c:A).
        integral f = zero ==> circleAverage integral add f c = zero`;;

let circleAverage_linear =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_integral integral add zero ==>
      !(f:A->A) (g:A->A) (c:A).
        circleAverage integral add (\z. add (f z) (g z)) c =
        add (circleAverage integral add f c) (circleAverage integral add g c)`;;

let circleAverage_shift_commute =
  `!(zero:A) (add:A->A->A) (integral:(A->A)->A).
      is_add_monoid zero add /\ is_integral integral add zero ==>
      !(f:A->A) (c:A) (d:A).
        circleAverage integral add (\z. f (circleMap add d z)) c =
        circleAverage integral add f (add c d)`;;
