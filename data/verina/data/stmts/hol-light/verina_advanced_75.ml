(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_75,
  catalog title "task_code": an executable Kadane scan computes the maximum
  sum of a nonempty contiguous subarray of a nonempty integer sequence, with
  an exhaustive membership-and-maximality correctness contract. This file
  contains no proof.
*)

let task_code_precond = new_definition
  `task_code_precond (sequence:int list) <=>
     0 < LENGTH sequence`;;

let task_code_max = new_definition
  `task_code_max (a:int) (b:int) =
     if a <= b then b else a`;;

let task_code_fold =
  new_recursive_definition list_RECURSION
    `(!cur:int. !maxSoFar:int.
        task_code_fold
          ([]:int list) cur maxSoFar =
        maxSoFar) /\
     (!x:int. !xs:int list. !cur:int. !maxSoFar:int.
        task_code_fold
          (CONS x xs) cur maxSoFar =
        let newCur =
          task_code_max x (cur + x) in
        let newMax =
          task_code_max maxSoFar newCur in
        task_code_fold xs newCur newMax)`;;

let task_code = new_definition
  `task_code (sequence:int list) =
     if sequence = [] then (&0:int)
     else
       task_code_fold
         (TL sequence) (HD sequence) (HD sequence)`;;

let task_code_range =
  new_recursive_definition num_RECURSION
    `(task_code_range 0 = []) /\
     (!n:num.
        task_code_range (SUC n) =
        APPEND
          (task_code_range n)
          (CONS n []))`;;

let task_code_positiveLengths = new_definition
  `task_code_positiveLengths (n:num) =
     MAP SUC (task_code_range n)`;;

let task_code_drop =
  new_recursive_definition num_RECURSION
    `(!sequence:int list.
        task_code_drop 0 sequence = sequence) /\
     (!n:num. !sequence:int list.
        task_code_drop (SUC n) sequence =
        if sequence = [] then []
        else task_code_drop n (TL sequence))`;;

let task_code_take =
  new_recursive_definition num_RECURSION
    `(!sequence:int list.
        task_code_take 0 sequence = []) /\
     (!n:num. !sequence:int list.
        task_code_take (SUC n) sequence =
        if sequence = [] then []
        else
          CONS (HD sequence)
            (task_code_take n (TL sequence)))`;;

let task_code_sum =
  new_recursive_definition list_RECURSION
    `(task_code_sum ([]:int list) = (&0:int)) /\
     (!x:int. !xs:int list.
        task_code_sum (CONS x xs) =
        x + task_code_sum xs)`;;

let task_code_sumsAt = new_definition
  `task_code_sumsAt
      (sequence:int list) (start:num) =
     MAP
       (\len:num.
          task_code_sum
            (task_code_take len
              (task_code_drop start sequence)))
       (task_code_positiveLengths
         (LENGTH sequence - start))`;;

let task_code_allSumsFrom =
  new_recursive_definition list_RECURSION
    `(!sequence:int list.
        task_code_allSumsFrom
          sequence ([]:num list) = []) /\
     (!start:num. !starts:num list. !sequence:int list.
        task_code_allSumsFrom
          sequence (CONS start starts) =
        APPEND
          (task_code_sumsAt sequence start)
          (task_code_allSumsFrom sequence starts))`;;

let task_code_subArraySums = new_definition
  `task_code_subArraySums (sequence:int list) =
     task_code_allSumsFrom
       sequence
       (task_code_range (LENGTH sequence + 1))`;;

let task_code_postcond = new_definition
  `task_code_postcond
      (sequence:int list) (result:int) <=>
     let subArraySums =
       task_code_subArraySums sequence in
     MEM result subArraySums /\
     ALL (\s:int. s <= result) subArraySums`;;

let task_code_spec_satisfied =
  `!sequence:int list.
     task_code_precond sequence
     ==> task_code_postcond
           sequence (task_code sequence)`;;
