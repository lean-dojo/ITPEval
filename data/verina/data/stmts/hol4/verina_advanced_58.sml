(*
  Statement-only formalization of VERINA artifact verina_advanced_58,
  cataloged as "nthUglyNumber": the executable three-index generator returns
  the requested positive natural number whose only prime factors are 2, 3,
  and 5, with exactly n - 1 smaller ugly numbers. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory listTheory pairTheory;

val nthUglyNumber_precond_def = new_definition (
  "nthUglyNumber_precond_def",
  ``nthUglyNumber_precond (n : num) <=> 0 < n``
);

val nthUglyNumber_getAt_def = new_definition (
  "nthUglyNumber_getAt_def",
  ``nthUglyNumber_getAt (seq : num list) (index : num) =
      case DROP index seq of
        [] => 0
      | x::xs => x``
);

val nextUgly_def = new_definition (
  "nextUgly_def",
  ``nextUgly
      (seq : num list) (c2 : num) (c3 : num) (c5 : num) =
      let i2 = nthUglyNumber_getAt seq c2 * 2 in
      let i3 = nthUglyNumber_getAt seq c3 * 3 in
      let i5 = nthUglyNumber_getAt seq c5 * 5 in
      let min35 = if i3 <= i5 then i3 else i5 in
      let next = if i2 <= min35 then i2 else min35 in
      let c2' = if next = i2 then c2 + 1 else c2 in
      let c3' = if next = i3 then c3 + 1 else c3 in
      let c5' = if next = i5 then c5 + 1 else c5 in
        (next,(c2',(c3',c5')))``
);

val nthUglyNumber_loop_def = Define `
  (nthUglyNumber_loop
      0
      (seq : num list)
      (c2 : num)
      (c3 : num)
      (c5 : num) =
     seq) /\
  (nthUglyNumber_loop
      (SUC i) seq c2 c3 c5 =
     let updated = nextUgly seq c2 c3 c5 in
       nthUglyNumber_loop
         i
         (seq ++ [FST updated])
         (FST (SND updated))
         (FST (SND (SND updated)))
         (SND (SND (SND updated))))
`;

val nthUglyNumber_def = new_definition (
  "nthUglyNumber_def",
  ``nthUglyNumber (n : num) =
      nthUglyNumber_getAt
        (nthUglyNumber_loop (n - 1) [1] 0 0 0)
        (n - 1)``
);

val divideOutFuel_def = Define `
  (divideOutFuel 0 (n : num) (p : num) = n) /\
  (divideOutFuel (SUC fuel) n p =
     if 1 < p /\ 0 < n /\ n MOD p = 0 then
       divideOutFuel fuel (n DIV p) p
     else
       n)
`;

val divideOut_def = new_definition (
  "divideOut_def",
  ``divideOut (n : num) (p : num) = divideOutFuel n n p``
);

val isUgly_def = new_definition (
  "isUgly_def",
  ``isUgly (x : num) <=>
      if x = 0 then
        F
      else
        let n1 = divideOut x 2 in
        let n2 = divideOut n1 3 in
        let n3 = divideOut n2 5 in
          n3 = 1``
);

val nthUglyNumber_postcond_def = new_definition (
  "nthUglyNumber_postcond_def",
  ``nthUglyNumber_postcond (n : num) (result : num) <=>
      isUgly result /\
      LENGTH (FILTER isUgly (COUNT_LIST result)) = n - 1``
);

val nthUglyNumber_spec_satisfied =
  ``!n : num.
      nthUglyNumber_precond n ==>
      nthUglyNumber_postcond n (nthUglyNumber n)``;
