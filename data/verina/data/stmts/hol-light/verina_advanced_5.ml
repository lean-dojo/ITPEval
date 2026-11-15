(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_5,
  catalog title "addTwoNumbers": executable reverse-order decimal-list
  addition with carry for canonical nonempty digit lists, together with its
  numeric-value, digit-bound, and canonical-form correctness contract. This
  file contains no proof.
*)

let listToNat =
  new_recursive_definition list_RECURSION
    `(listToNat ([]:num list) = 0) /\
     (!d:num. !ds:num list.
        listToNat (CONS d ds) =
        d + 10 * listToNat ds)`;;

let addTwoNumbers_lastOrZero =
  new_recursive_definition list_RECURSION
    `(addTwoNumbers_lastOrZero ([]:num list) = 0) /\
     (!d:num. !ds:num list.
        addTwoNumbers_lastOrZero (CONS d ds) =
        if ds = [] then d
        else addTwoNumbers_lastOrZero ds)`;;

let addTwoNumbers_precond = new_definition
  `addTwoNumbers_precond
      (l1:num list) (l2:num list) <=>
     0 < LENGTH l1 /\
     0 < LENGTH l2 /\
     ALL (\d:num. d < 10) l1 /\
     ALL (\d:num. d < 10) l2 /\
     (~(addTwoNumbers_lastOrZero l1 = 0) \/
      l1 = CONS 0 []) /\
     (~(addTwoNumbers_lastOrZero l2 = 0) \/
      l2 = CONS 0 [])`;;

let addTwoNumbers_addAuxFuel =
  new_recursive_definition num_RECURSION
    `(!l1:num list. !l2:num list. !carry:num.
        addTwoNumbers_addAuxFuel 0 l1 l2 carry =
        if l1 = [] then
          if l2 = [] then
            if carry = 0 then [] else CONS carry []
          else []
        else []) /\
     (!fuel:num. !l1:num list. !l2:num list. !carry:num.
        addTwoNumbers_addAuxFuel (SUC fuel) l1 l2 carry =
        if l1 = [] then
          if l2 = [] then
            if carry = 0 then [] else CONS carry []
          else
            let h2 = HD l2 in
            let t2 = TL l2 in
            let sum = h2 + carry in
            CONS (sum MOD 10)
              (addTwoNumbers_addAuxFuel
                fuel [] t2 (sum DIV 10))
        else if l2 = [] then
          let h1 = HD l1 in
          let t1 = TL l1 in
          let sum = h1 + carry in
          CONS (sum MOD 10)
            (addTwoNumbers_addAuxFuel
              fuel t1 [] (sum DIV 10))
        else
          let h1 = HD l1 in
          let t1 = TL l1 in
          let h2 = HD l2 in
          let t2 = TL l2 in
          let sum = h1 + h2 + carry in
          CONS (sum MOD 10)
            (addTwoNumbers_addAuxFuel
              fuel t1 t2 (sum DIV 10)))`;;

let addTwoNumbers_addAux = new_definition
  `addTwoNumbers_addAux
      (l1:num list) (l2:num list) (carry:num) =
     addTwoNumbers_addAuxFuel
       (LENGTH l1 + LENGTH l2) l1 l2 carry`;;

let addTwoNumbers = new_definition
  `addTwoNumbers (l1:num list) (l2:num list) =
     addTwoNumbers_addAux l1 l2 0`;;

let addTwoNumbers_postcond = new_definition
  `addTwoNumbers_postcond
      (l1:num list) (l2:num list) (result:num list) <=>
     listToNat result = listToNat l1 + listToNat l2 /\
     ALL (\d:num. d < 10) result /\
     (~(addTwoNumbers_lastOrZero result = 0) \/
      (l1 = CONS 0 [] /\
       l2 = CONS 0 [] /\
       result = CONS 0 []))`;;

let addTwoNumbers_spec_satisfied =
  `!l1:num list. !l2:num list.
     addTwoNumbers_precond l1 l2
     ==> addTwoNumbers_postcond
           l1 l2 (addTwoNumbers l1 l2)`;;
