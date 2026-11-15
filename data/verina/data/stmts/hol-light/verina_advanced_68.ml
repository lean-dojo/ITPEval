(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_68,
  catalog title "runLengthEncoder": an executable Unicode-string run-length
  encoder converts digit-free input to character/count text, with exact
  format, decoding, and empty-string correctness conditions. This file
  contains no proof.
*)

let runLengthEncoder_validChar = new_definition
  `runLengthEncoder_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let runLengthEncoder_string = new_definition
  `runLengthEncoder_string (s:num list) <=>
     ALL runLengthEncoder_validChar s`;;

let runLengthEncoder_isDigit = new_definition
  `runLengthEncoder_isDigit (c:num) <=>
     48 <= c /\ c <= 57`;;

let runLengthEncoder_precond = new_definition
  `runLengthEncoder_precond (input:num list) <=>
     ALL (\c:num. ~runLengthEncoder_isDigit c) input`;;

let runLengthEncoder_numToDigits = define
  `runLengthEncoder_numToDigits (n:num) =
     if n < 10 then
       CONS (n + 48) []
     else
       APPEND
         (runLengthEncoder_numToDigits (n DIV 10))
         (CONS (n MOD 10 + 48) [])`;;

let runLengthEncoder_optionValue =
  new_recursive_definition option_RECURSION
    `(runLengthEncoder_optionValue (NONE:num option) = 0) /\
     (!x:num.
        runLengthEncoder_optionValue (SOME x) = x)`;;

let runLengthEncoder_encodeSome =
  new_recursive_definition list_RECURSION
    `(!current:num. !count:num.
        runLengthEncoder_encodeSome
          ([]:num list) current count =
        CONS current (runLengthEncoder_numToDigits count)) /\
     (!c:num. !rest:num list. !current:num. !count:num.
        runLengthEncoder_encodeSome
          (CONS c rest) current count =
        if c = current then
          runLengthEncoder_encodeSome
            rest current (count + 1)
        else
          APPEND
            (CONS current
              (runLengthEncoder_numToDigits count))
            (runLengthEncoder_encodeSome rest c 1))`;;

let runLengthEncoder_encode = new_definition
  `runLengthEncoder_encode
      (remaining:num list)
      (currentChar:num option)
      (count:num) =
     if currentChar = NONE then
       if remaining = [] then []
       else
         runLengthEncoder_encodeSome
           (TL remaining) (HD remaining) 1
     else
       runLengthEncoder_encodeSome
         remaining
         (runLengthEncoder_optionValue currentChar)
         count`;;

let runLengthEncoder = new_definition
  `runLengthEncoder (input:num list) =
     if input = [] then []
     else
       runLengthEncoder_encode
         (TL input) (SOME (HD input)) 1`;;

let runLengthEncoder_parseState =
  new_recursive_definition list_RECURSION
    `(!currentChar:num option.
      !currentCount:num option.
      !acc:(num#num)list.
        runLengthEncoder_parseState
          ([]:num list) currentChar currentCount acc =
        if
          ~(currentChar = NONE) /\
          ~(currentCount = NONE)
        then
          CONS
            (runLengthEncoder_optionValue currentChar,
             runLengthEncoder_optionValue currentCount)
            acc
        else acc) /\
     (!c:num. !cs:num list.
      !currentChar:num option.
      !currentCount:num option.
      !acc:(num#num)list.
        runLengthEncoder_parseState
          (CONS c cs) currentChar currentCount acc =
        if runLengthEncoder_isDigit c then
          if currentChar = NONE then []
          else
            let digit = c - 48 in
            let newCount =
              if currentCount = NONE then digit
              else
                runLengthEncoder_optionValue currentCount *
                10 + digit in
            runLengthEncoder_parseState
              cs currentChar (SOME newCount) acc
        else
          let newAcc =
            if
              ~(currentChar = NONE) /\
              ~(currentCount = NONE)
            then
              CONS
                (runLengthEncoder_optionValue currentChar,
                 runLengthEncoder_optionValue currentCount)
                acc
            else acc in
          runLengthEncoder_parseState
            cs (SOME c) NONE newAcc)`;;

let runLengthEncoder_parseEncodedString = new_definition
  `runLengthEncoder_parseEncodedString (s:num list) =
     REVERSE
       (runLengthEncoder_parseState
         s NONE NONE [])`;;

let runLengthEncoder_checkPairs = define
  `runLengthEncoder_checkPairs
      ((chars:num list),nowDigit) =
     if chars = [] then T
     else
       let c = HD chars in
       let cs = TL chars in
       if nowDigit /\ runLengthEncoder_isDigit c then
         runLengthEncoder_checkPairs(cs,T)
       else if cs = [] then F
       else if runLengthEncoder_isDigit (HD cs) then
         runLengthEncoder_checkPairs(TL cs,T)
       else F`;;

let runLengthEncoder_expandPairs =
  new_recursive_definition list_RECURSION
    `(runLengthEncoder_expandPairs
        ([]:(num#num)list) = ([]:num list)) /\
     (!pair:num#num. !pairs:(num#num)list.
        runLengthEncoder_expandPairs
          (CONS pair pairs) =
        APPEND
          (REPLICATE (SND pair) (FST pair))
          (runLengthEncoder_expandPairs pairs))`;;

let runLengthEncoder_postcond = new_definition
  `runLengthEncoder_postcond
      (input:num list) (result:num list) <=>
     runLengthEncoder_string input /\
     runLengthEncoder_string result /\
     runLengthEncoder_checkPairs(result,F) /\
     runLengthEncoder_expandPairs
       (runLengthEncoder_parseEncodedString result) =
       input /\
     (input = [] <=> result = [])`;;

let runLengthEncoder_spec_satisfied =
  `!input:num list.
     runLengthEncoder_string input
     ==> runLengthEncoder_precond input
     ==> runLengthEncoder_postcond
           input (runLengthEncoder input)`;;
