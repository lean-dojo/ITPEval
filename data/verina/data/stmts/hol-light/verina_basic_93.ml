(*
  Statement-only formalization of VERINA corpus artifact verina_basic_93
  (verina__hol-light__verina_basic_93), catalog title "SwapBitvectors": an
  executable three-XOR computation swaps two 8-bit Boolean vectors, together
  with its total precondition and exact pair-valued correctness contract.
  This file contains no proof.
*)

let uint8_xor = new_definition
  `uint8_xor (x:bool^8) (y:bool^8) =
     ((lambda i. ~(x$i <=> y$i)):bool^8)`;;

let SwapBitvectors_precond = new_definition
  `SwapBitvectors_precond (X:bool^8) (Y:bool^8) <=> T`;;

let SwapBitvectors = new_definition
  `SwapBitvectors (X:bool^8) (Y:bool^8) =
     let temp = uint8_xor X Y in
     let newY = uint8_xor temp Y in
     let newX = uint8_xor temp newY in
     (newX,newY)`;;

let SwapBitvectors_postcond = new_definition
  `SwapBitvectors_postcond
      (X:bool^8) (Y:bool^8) (result:(bool^8)#(bool^8)) <=>
     FST result = Y /\
     SND result = X /\
     (~(X = Y)
      ==> ~(FST result = X) /\ ~(SND result = Y))`;;

let SwapBitvectors_spec_satisfied =
  `!X:bool^8. !Y:bool^8.
     SwapBitvectors_precond X Y
     ==> SwapBitvectors_postcond X Y (SwapBitvectors X Y)`;;
