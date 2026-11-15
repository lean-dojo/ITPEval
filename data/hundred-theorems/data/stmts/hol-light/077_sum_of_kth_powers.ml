(*
  Statement-only formalization of "Sum of kth Powers" from Hundred Theorems
  artifact 077 (hundred-theorems__hol-light__077). It states Faulhaber's
  formula using Bernoulli numbers and Bernoulli polynomials. This file
  contains no proof.
*)

needs "Library/binomial.ml";;

prioritize_real();;

let SUM_OF_POWERS =
  `!bernoulli bernpoly.
      bernoulli 0 = &1 /\
      (!r. bernoulli (SUC r) =
           --sum(0..r) (\j. &(binom(r + 2,j)) * bernoulli j) /
           (&r + &2)) /\
      (!r x. bernpoly r x =
             sum(0..r)
               (\k. &(binom(r,k)) * bernoulli k * x pow (r - k)))
      ==> !m n.
          sum(0..n) (\k. &k pow m) =
          (bernpoly (SUC m) (&n + &1) -
           bernpoly (SUC m) (&0)) /
          (&m + &1)`;;
