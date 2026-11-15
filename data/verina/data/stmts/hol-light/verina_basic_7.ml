(*
  Statement-only formalization of VERINA corpus artifact verina_basic_7
  (verina__hol-light__verina_basic_7), catalog title
  "sumOfSquaresOfFirstNOddNumbers": an executable natural-number recursion
  accumulates the squares of the first n odd numbers and is connected to its
  exact natural-division and truncated-subtraction correctness contract. This
  file contains no proof.
*)

let sumOfSquaresOfFirstNOddNumbers_precond = new_definition
  `sumOfSquaresOfFirstNOddNumbers_precond (n:num) <=> T`;;

let sumOfSquaresOfFirstNOddNumbers_loop =
  new_recursive_definition num_RECURSION
    `(!acc:num.
        sumOfSquaresOfFirstNOddNumbers_loop 0 acc = acc) /\
     (!k:num. !acc:num.
        sumOfSquaresOfFirstNOddNumbers_loop (SUC k) acc =
        sumOfSquaresOfFirstNOddNumbers_loop
          k
          (acc +
           (2 * SUC k - 1) * (2 * SUC k - 1)))`;;

let sumOfSquaresOfFirstNOddNumbers = new_definition
  `sumOfSquaresOfFirstNOddNumbers (n:num) =
     sumOfSquaresOfFirstNOddNumbers_loop n 0`;;

let sumOfSquaresOfFirstNOddNumbers_postcond = new_definition
  `sumOfSquaresOfFirstNOddNumbers_postcond
      (n:num) (result:num) <=>
     result - ((n * (2 * n - 1) * (2 * n + 1)) DIV 3) = 0 /\
     ((n * (2 * n - 1) * (2 * n + 1)) DIV 3) - result = 0`;;

let sumOfSquaresOfFirstNOddNumbers_spec_satisfied =
  `!n:num.
     sumOfSquaresOfFirstNOddNumbers_precond n
     ==> sumOfSquaresOfFirstNOddNumbers_postcond
           n (sumOfSquaresOfFirstNOddNumbers n)`;;
