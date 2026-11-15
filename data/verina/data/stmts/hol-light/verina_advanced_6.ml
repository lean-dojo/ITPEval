(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_6,
  catalog title "allVowels": an executable case-insensitive Unicode-string
  test lowercases ASCII letters and checks that all five English vowels occur,
  together with its total correctness contract. This file contains no proof.
*)

let allVowels_validChar = new_definition
  `allVowels_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let allVowels_string = new_definition
  `allVowels_string (s:num list) <=>
     ALL allVowels_validChar s`;;

let toLower = new_definition
  `toLower (c:num) =
     if 65 <= c /\ c <= 90 then c + 32 else c`;;

let normalize_str = new_definition
  `normalize_str (s:num list) = MAP toLower s`;;

let allVowels_precond = new_definition
  `allVowels_precond (s:num list) <=> T`;;

let allVowels_vowelSet = new_definition
  `allVowels_vowelSet = [97; 101; 105; 111; 117]`;;

let allVowels = new_definition
  `allVowels (s:num list) =
     ALL (\v:num. MEM v (normalize_str s)) allVowels_vowelSet`;;

let allVowels_postcond = new_definition
  `allVowels_postcond (s:num list) (result:bool) <=>
     (result <=>
      ALL (\v:num. MEM v (normalize_str s)) allVowels_vowelSet)`;;

let allVowels_spec_satisfied =
  `!s:num list.
     allVowels_string s
     ==> allVowels_precond s
     ==> allVowels_postcond s (allVowels s)`;;
