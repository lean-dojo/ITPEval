(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_7,
  catalog title "binaryToDecimal": an executable recursive conversion of a
  big-endian list of binary natural-number digits to its decimal value,
  together with its precondition and fold-based correctness contract. This
  file contains no proof.
*)

let binaryToDecimal_precond = new_definition
  `binaryToDecimal_precond (digits:num list) <=>
     ALL (\d:num. d = 0 \/ d = 1) digits`;;

let binaryToDecimal_helper =
  new_recursive_definition list_RECURSION
    `(binaryToDecimal_helper ([]:num list) = 0) /\
     (!first:num. !rest:num list.
        binaryToDecimal_helper (CONS first rest) =
        first * (2 EXP (LENGTH rest)) +
        binaryToDecimal_helper rest)`;;

let binaryToDecimal = new_definition
  `binaryToDecimal (digits:num list) =
     binaryToDecimal_helper digits`;;

let binaryToDecimal_foldl =
  new_recursive_definition list_RECURSION
    `(!acc:num.
        binaryToDecimal_foldl ([]:num list) acc = acc) /\
     (!first:num. !rest:num list. !acc:num.
        binaryToDecimal_foldl (CONS first rest) acc =
        binaryToDecimal_foldl rest (acc * 2 + first))`;;

let binaryToDecimal_postcond = new_definition
  `binaryToDecimal_postcond
      (digits:num list) (result:num) <=>
     let value = binaryToDecimal_foldl digits 0 in
     result - value = 0 /\
     value - result = 0`;;

let binaryToDecimal_spec_satisfied =
  `!digits:num list.
     binaryToDecimal_precond digits
     ==> binaryToDecimal_postcond
           digits (binaryToDecimal digits)`;;
