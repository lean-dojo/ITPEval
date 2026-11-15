(*
  Statement-only formalization of VERINA corpus artifact verina_basic_30
  (verina__hol-light__verina_basic_30), catalog title "elementWiseModulo": an
  executable element-wise Euclidean remainder operation on two integer arrays,
  together with its equal nonzero-length, nonzero-divisor precondition and
  pointwise correctness contract. This file contains no proof.
*)

let elementWiseModulo_precond = new_definition
  `elementWiseModulo_precond (a:int list) (b:int list) <=>
     LENGTH a = LENGTH b /\
     0 < LENGTH a /\
     (!i:num.
        i < LENGTH b
        ==> ~(EL i b = (&0:int)))`;;

let elementWiseModulo =
  new_recursive_definition list_RECURSION
    `(!b:int list.
        elementWiseModulo ([]:int list) b = []) /\
     (!x:int. !xs:int list. !b:int list.
        elementWiseModulo (CONS x xs) b =
        if b = [] then
          CONS (x rem (&0:int))
            (elementWiseModulo xs ([]:int list))
        else
          CONS (x rem (HD b))
            (elementWiseModulo xs (TL b)))`;;

let elementWiseModulo_postcond = new_definition
  `elementWiseModulo_postcond
      (a:int list) (b:int list) (result:int list) <=>
     LENGTH result = LENGTH a /\
     (!i:num.
        i < LENGTH result
        ==> EL i result = (EL i a) rem (EL i b))`;;

let elementWiseModulo_spec_satisfied =
  `!a:int list. !b:int list.
     elementWiseModulo_precond a b
     ==> elementWiseModulo_postcond
           a b (elementWiseModulo a b)`;;
