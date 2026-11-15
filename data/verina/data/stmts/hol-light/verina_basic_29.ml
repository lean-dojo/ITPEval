(*
  Statement-only formalization of VERINA corpus artifact verina_basic_29
  (verina__hol-light__verina_basic_29), catalog title "removeElement": a
  deterministic recursive operation removes the integer at a valid natural
  index, with the resulting length and shifted-element correctness contract.
  This file contains no proof.
*)

let removeElement_precond = new_definition
  `removeElement_precond (s:int list) (k:num) <=>
     k < LENGTH s`;;

let removeElement_eraseIdx =
  new_recursive_definition num_RECURSION
    `(!s:int list.
        removeElement_eraseIdx 0 s =
        if s = [] then [] else TL s) /\
     (!k:num. !s:int list.
        removeElement_eraseIdx (SUC k) s =
        if s = [] then []
        else CONS (HD s) (removeElement_eraseIdx k (TL s)))`;;

let removeElement = new_definition
  `removeElement (s:int list) (k:num) =
     removeElement_eraseIdx k s`;;

let removeElement_postcond = new_definition
  `removeElement_postcond
      (s:int list) (k:num) (result:int list) <=>
     LENGTH result = LENGTH s - 1 /\
     (!i:num.
        i < k
        ==> EL i result = EL i s) /\
     (!i:num.
        i < LENGTH result
        ==> k <= i
        ==> EL i result = EL (i + 1) s)`;;

let removeElement_spec_satisfied =
  `!s:int list. !k:num.
     removeElement_precond s k
     ==> removeElement_postcond
           s k (removeElement s k)`;;
