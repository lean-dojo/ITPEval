(*
  Statement-only formalization of VERINA corpus artifact verina_basic_79,
  catalog title "onlineMax": the executable integer-array program computes the
  maximum of the first x entries and then finds the first later entry exceeding
  it, or the final index if none does, under its correctness contract. This
  file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory integerTheory listTheory pairTheory;

val onlineMax_precond_def = new_definition (
  "onlineMax_precond_def",
  ``onlineMax_precond (a : int list) (x : num) <=>
      LENGTH a > 0 /\ x > 0 /\ x < LENGTH a``
);

val onlineMax_nthD_def = Define `
  (onlineMax_nthD
      ([] : int list) (index : num) = (0 : int)) /\
  (onlineMax_nthD
      (value::rest) 0 = value) /\
  (onlineMax_nthD
      (value::rest) (SUC index) =
     onlineMax_nthD rest index)
`;

val findBestFuel_def = Define `
  (findBestFuel
      0
      (a : int list)
      (x : num)
      (i : num)
      (best : int) =
     best) /\
  (findBestFuel
      (SUC fuel)
      a
      x
      i
      best =
     if i < x then
       let newBest =
         if onlineMax_nthD a i > best then
           onlineMax_nthD a i
         else
           best
       in
         findBestFuel fuel a x (i + 1) newBest
     else
       best)
`;

val findBest_def = new_definition (
  "findBest_def",
  ``findBest
      (a : int list) (x : num) (i : num) (best : int) =
      findBestFuel (x - i) a x i best``
);

val findPFuel_def = Define `
  (findPFuel
      0
      (a : int list)
      (x : num)
      (m : int)
      (i : num) =
     LENGTH a - 1) /\
  (findPFuel
      (SUC fuel)
      a
      x
      m
      i =
     if i < LENGTH a then
       if onlineMax_nthD a i > m then
         i
       else
         findPFuel fuel a x m (i + 1)
     else
       LENGTH a - 1)
`;

val findP_def = new_definition (
  "findP_def",
  ``findP
      (a : int list) (x : num) (m : int) (i : num) =
      findPFuel (LENGTH a - i) a x m i``
);

val onlineMax_def = new_definition (
  "onlineMax_def",
  ``onlineMax (a : int list) (x : num) =
      let best = onlineMax_nthD a 0 in
      let m = findBest a x 1 best in
      let p = findP a x m x in
        (m, p)``
);

val onlineMax_postcond_def = new_definition (
  "onlineMax_postcond_def",
  ``onlineMax_postcond
      (a : int list) (x : num) (result : int # num) <=>
      let m = FST result in
      let p = SND result in
        (x <= p /\ p < LENGTH a) /\
        (!i : num.
           i < x ==>
           onlineMax_nthD a i <= m) /\
        (?i : num.
           i < x /\
           onlineMax_nthD a i = m) /\
        (!i : num.
           x <= i ==>
           i < p ==>
           onlineMax_nthD a i <= m) /\
        (onlineMax_nthD a p > m \/
         (p = LENGTH a - 1 /\
          !i : num.
            x <= i ==>
            i < LENGTH a ==>
            onlineMax_nthD a i <= m))``
);

val onlineMax_spec_satisfied =
  ``!(a : int list) (x : num).
      onlineMax_precond a x ==>
      onlineMax_postcond a x (onlineMax a x)``;
