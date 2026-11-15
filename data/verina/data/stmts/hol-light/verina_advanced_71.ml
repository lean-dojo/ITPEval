(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_71,
  catalog title "shortestBeautifulSubstring": an executable binary-string
  search returns the shortest nonempty contiguous substring containing exactly
  k ones, breaking length ties lexicographically, together with its correctness
  contract. This file contains no proof.
*)

let shortestBeautifulSubstring_validChar = new_definition
  `shortestBeautifulSubstring_validChar (c:num) <=>
     c < 55296 \/ (57343 < c /\ c < 1114112)`;;

let shortestBeautifulSubstring_string = new_definition
  `shortestBeautifulSubstring_string (s:num list) <=>
     ALL shortestBeautifulSubstring_validChar s`;;

let shortestBeautifulSubstring_countOnes =
  new_recursive_definition list_RECURSION
    `(shortestBeautifulSubstring_countOnes ([]:num list) = 0) /\
     (!c:num. !cs:num list.
        shortestBeautifulSubstring_countOnes (CONS c cs) =
        (if c = 49 then 1 else 0) +
        shortestBeautifulSubstring_countOnes cs)`;;

let shortestBeautifulSubstring_precond = new_definition
  `shortestBeautifulSubstring_precond
      (s:num list) (k:num) <=>
     ALL (\c:num. c = 48 \/ c = 49) s`;;

let shortestBeautifulSubstring_listToString = new_definition
  `shortestBeautifulSubstring_listToString
      (chars:num list) = chars`;;

let shortestBeautifulSubstring_isLexSmaller =
  new_recursive_definition list_RECURSION
    `(!b:num list.
        shortestBeautifulSubstring_isLexSmaller
          ([]:num list) b <=> ~(b = [])) /\
     (!a:num. !as':num list. !b:num list.
        shortestBeautifulSubstring_isLexSmaller
          (CONS a as') b <=>
        if b = [] then F
        else
          a < HD b \/
          (a = HD b /\
           shortestBeautifulSubstring_isLexSmaller
             as' (TL b)))`;;

let shortestBeautifulSubstring_lexLe = new_definition
  `shortestBeautifulSubstring_lexLe
     (a:num list) (b:num list) <=>
     a = b \/
     shortestBeautifulSubstring_isLexSmaller a b`;;

let shortestBeautifulSubstring_range =
  new_recursive_definition num_RECURSION
    `(shortestBeautifulSubstring_range 0 = []) /\
     (!n:num.
        shortestBeautifulSubstring_range (SUC n) =
        APPEND
          (shortestBeautifulSubstring_range n)
          (CONS n []))`;;

let shortestBeautifulSubstring_drop =
  new_recursive_definition num_RECURSION
    `(!chars:num list.
        shortestBeautifulSubstring_drop 0 chars = chars) /\
     (!n:num. !chars:num list.
        shortestBeautifulSubstring_drop (SUC n) chars =
        if chars = [] then []
        else
          shortestBeautifulSubstring_drop n (TL chars))`;;

let shortestBeautifulSubstring_take =
  new_recursive_definition num_RECURSION
    `(!chars:num list.
        shortestBeautifulSubstring_take 0 chars = []) /\
     (!n:num. !chars:num list.
        shortestBeautifulSubstring_take (SUC n) chars =
        if chars = [] then []
        else
          CONS (HD chars)
            (shortestBeautifulSubstring_take n (TL chars)))`;;

let shortestBeautifulSubstring_nonemptyAt = new_definition
  `shortestBeautifulSubstring_nonemptyAt
      (chars:num list) (start:num) =
     MAP
       (\j:num.
          shortestBeautifulSubstring_take (j + 1)
            (shortestBeautifulSubstring_drop start chars))
       (shortestBeautifulSubstring_range
         (LENGTH chars - start))`;;

let shortestBeautifulSubstring_nonemptyFrom =
  new_recursive_definition list_RECURSION
    `(!chars:num list.
        shortestBeautifulSubstring_nonemptyFrom
          chars ([]:num list) = []) /\
     (!start:num. !starts:num list. !chars:num list.
        shortestBeautifulSubstring_nonemptyFrom
          chars (CONS start starts) =
        APPEND
          (shortestBeautifulSubstring_nonemptyAt
            chars start)
          (shortestBeautifulSubstring_nonemptyFrom
            chars starts))`;;

let shortestBeautifulSubstring_allSubstrings = new_definition
  `shortestBeautifulSubstring_allSubstrings
      (chars:num list) =
     shortestBeautifulSubstring_nonemptyFrom
       chars
       (shortestBeautifulSubstring_range
         (LENGTH chars))`;;

let shortestBeautifulSubstring_compare = new_definition
  `shortestBeautifulSubstring_compare
      (a:num list) (b:num list) <=>
     LENGTH a < LENGTH b \/
     (LENGTH a = LENGTH b /\
      shortestBeautifulSubstring_isLexSmaller a b)`;;

let shortestBeautifulSubstring_optionValue =
  new_recursive_definition option_RECURSION
    `(shortestBeautifulSubstring_optionValue
        (NONE:(num list)option) = []) /\
     (!chars:num list.
        shortestBeautifulSubstring_optionValue
          (SOME chars) = chars)`;;

let shortestBeautifulSubstring_updateBest = new_definition
  `shortestBeautifulSubstring_updateBest
      (best:(num list)option) (current:num list) =
     if best = NONE then SOME current
     else
       let previous =
         shortestBeautifulSubstring_optionValue best in
       if shortestBeautifulSubstring_compare
            current previous
       then SOME current
       else SOME previous`;;

let shortestBeautifulSubstring_foldCandidates =
  new_recursive_definition list_RECURSION
    `(!best:(num list)option.
        shortestBeautifulSubstring_foldCandidates
          ([]:(num list)list) best = best) /\
     (!current:num list. !rest:(num list)list.
      !best:(num list)option.
        shortestBeautifulSubstring_foldCandidates
          (CONS current rest) best =
        shortestBeautifulSubstring_foldCandidates
          rest
          (shortestBeautifulSubstring_updateBest
            best current))`;;

let shortestBeautifulSubstring = new_definition
  `shortestBeautifulSubstring
      (s:num list) (k:num) =
     let chars = s in
     let candidates =
       FILTER
         (\sub:num list.
            shortestBeautifulSubstring_countOnes sub = k)
         (shortestBeautifulSubstring_allSubstrings
           chars) in
     let best =
       shortestBeautifulSubstring_foldCandidates
         candidates (NONE:(num list)option) in
     if best = NONE then []
     else
       shortestBeautifulSubstring_listToString
         (shortestBeautifulSubstring_optionValue best)`;;

let shortestBeautifulSubstring_slicesAt = new_definition
  `shortestBeautifulSubstring_slicesAt
      (chars:num list) (start:num) =
     MAP
       (\len:num.
          shortestBeautifulSubstring_take len
            (shortestBeautifulSubstring_drop
              start chars))
       (shortestBeautifulSubstring_range
         (LENGTH chars - start + 1))`;;

let shortestBeautifulSubstring_slicesFrom =
  new_recursive_definition list_RECURSION
    `(!chars:num list.
        shortestBeautifulSubstring_slicesFrom
          chars ([]:num list) = []) /\
     (!start:num. !starts:num list. !chars:num list.
        shortestBeautifulSubstring_slicesFrom
          chars (CONS start starts) =
        APPEND
          (shortestBeautifulSubstring_slicesAt
            chars start)
          (shortestBeautifulSubstring_slicesFrom
            chars starts))`;;

let shortestBeautifulSubstring_postSubstrings =
  new_definition
    `shortestBeautifulSubstring_postSubstrings
        (chars:num list) =
       shortestBeautifulSubstring_slicesFrom
         chars
         (shortestBeautifulSubstring_range
           (LENGTH chars))`;;

let shortestBeautifulSubstring_postcond = new_definition
  `shortestBeautifulSubstring_postcond
      (s:num list) (k:num) (result:num list) <=>
     let chars = s in
     let substrings =
       shortestBeautifulSubstring_postSubstrings
         chars in
     let beautiful =
       FILTER
         (\sub:num list.
            shortestBeautifulSubstring_countOnes sub = k)
         substrings in
     let targets =
       FILTER
         (\target:num list. ~(target = []))
         (MAP
           shortestBeautifulSubstring_listToString
           beautiful) in
     (result = [] /\ targets = []) \/
     (MEM result targets /\
      ALL
        (\r:num list.
           LENGTH r > LENGTH result \/
           (LENGTH r = LENGTH result /\
            shortestBeautifulSubstring_lexLe result r))
        targets)`;;

let shortestBeautifulSubstring_spec_satisfied =
  `!s:num list. !k:num.
     shortestBeautifulSubstring_string s
     ==> shortestBeautifulSubstring_precond s k
     ==> shortestBeautifulSubstring_postcond
           s k (shortestBeautifulSubstring s k)`;;
