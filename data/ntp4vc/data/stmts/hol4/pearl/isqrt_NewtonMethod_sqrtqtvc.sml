(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/isqrt_NewtonMethod_sqrtqtvc: the integer-square-root Newton-method
  verification condition, including its quadratic specification,
  initialization, and universally quantified loop preservation. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory;

val isqrt_NewtonMethod_sqrtqtvc_statement =
  ``let sqr =
      \z : int. z * z
    in
    let isqrt_spec =
      \z : int. \res : int.
        (0 : int) <= res /\
        sqr res <= z /\
        z < sqr (res + (1 : int))
    in
    let newton =
      \z : int. \y : int.
        ((z quot y) + y) quot (2 : int)
    in
      !x : int.
        (0 : int) <= x
        ==>
        if x = (0 : int) then
          isqrt_spec x (0 : int)
        else if x <= (3 : int) then
          isqrt_spec x (1 : int)
        else
          ~((2 : int) = (0 : int)) /\
          (let o1 =
             ((1 : int) + x) quot (2 : int)
           in
             ((0 : int) < o1 /\
              (0 : int) < x /\
              o1 = newton x x /\
              x < sqr (x + (1 : int)) /\
              x < sqr (o1 + (1 : int))) /\
             (!y : int.
                (0 : int) < newton x y /\
                (0 : int) < y /\
                x < sqr (y + (1 : int)) /\
                x < sqr (newton x y + (1 : int))
                ==>
                if newton x y < y then
                  ~(newton x y = (0 : int)) /\
                  ~((2 : int) = (0 : int)) /\
                  ((0 : int) <= y /\ newton x y < y) /\
                  (0 : int) < newton x (newton x y) /\
                  (0 : int) < newton x y /\
                  x < sqr (newton x y + (1 : int)) /\
                  x < sqr
                    (newton x (newton x y) + (1 : int))
                else
                  isqrt_spec x y))``;
