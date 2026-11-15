(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_67,
  catalog title "runLengthEncode": an executable accumulator-based scan groups
  consecutive equal characters of a Unicode string into positive run lengths,
  with adjacency and exact decoding correctness conditions. This file contains
  no proof.
*)

let runLengthEncode_validChar = new_definition
  `runLengthEncode_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let runLengthEncode_string = new_definition
  `runLengthEncode_string (s:num list) <=>
     ALL runLengthEncode_validChar s`;;

let runLengthEncode_precond = new_definition
  `runLengthEncode_precond (s:num list) <=> T`;;

let runLengthEncode_encodeAux =
  new_recursive_definition list_RECURSION
    `(!acc:(num#num)list.
        runLengthEncode_encodeAux acc ([]:num list) =
        REVERSE acc) /\
     (!h:num. !t:num list. !acc:(num#num)list.
        runLengthEncode_encodeAux acc (CONS h t) =
        if acc = [] then
          runLengthEncode_encodeAux
            (CONS (h,1) []) t
        else
          let current = HD acc in
          if FST current = h then
            runLengthEncode_encodeAux
              (CONS (FST current,SND current + 1) (TL acc)) t
          else
            runLengthEncode_encodeAux
              (CONS (h,1) acc) t)`;;

let runLengthEncode = new_definition
  `runLengthEncode (s:num list) =
     runLengthEncode_encodeAux [] s`;;

let decodeRLE =
  new_recursive_definition list_RECURSION
    `(decodeRLE ([]:(num#num)list) = ([]:num list)) /\
     (!run:num#num. !tail:(num#num)list.
        decodeRLE (CONS run tail) =
        APPEND
          (REPLICATE (SND run) (FST run))
          (decodeRLE tail))`;;

let runLengthEncode_postcond = new_definition
  `runLengthEncode_postcond
      (s:num list) (result:(num#num)list) <=>
     ALL (\run:num#num. 0 < SND run) result /\
     (!i:num.
        i < LENGTH result - 1
        ==> ~(FST (EL i result) =
              FST (EL (i + 1) result))) /\
     decodeRLE result = s`;;

let runLengthEncode_spec_satisfied =
  `!s:num list.
     runLengthEncode_string s
     ==> runLengthEncode_precond s
     ==> runLengthEncode_postcond
           s (runLengthEncode s)`;;
