(*
  Statement-only formalization of VERINA corpus artifact verina_advanced_58,
  catalog title "nthUglyNumber": an executable three-counter sequence
  computation returns the nth ugly number, with ugliness characterized by
  repeated division by 2, 3, and 5 and by its zero-based rank among smaller
  natural numbers. This file contains no proof.
*)

let nthUglyNumber_precond = new_definition
  `nthUglyNumber_precond (n:num) <=>
     n > 0`;;

let nthUglyNumber_get =
  new_recursive_definition num_RECURSION
    `(!seq:num list.
        nthUglyNumber_get 0 seq =
        if seq = [] then 0 else HD seq) /\
     (!index:num. !seq:num list.
        nthUglyNumber_get (SUC index) seq =
        if seq = [] then 0
        else nthUglyNumber_get index (TL seq))`;;

let nextUgly = new_definition
  `nextUgly
      (seq:num list) (c2:num) (c3:num) (c5:num) =
     let i2 = nthUglyNumber_get c2 seq * 2 in
     let i3 = nthUglyNumber_get c3 seq * 3 in
     let i5 = nthUglyNumber_get c5 seq * 5 in
     let next = MIN i2 (MIN i3 i5) in
     let c2' = if next = i2 then c2 + 1 else c2 in
     let c3' = if next = i3 then c3 + 1 else c3 in
     let c5' = if next = i5 then c5 + 1 else c5 in
     (next,(c2',(c3',c5')))`;;

let nthUglyNumber_loop =
  new_recursive_definition num_RECURSION
    `(!seq:num list. !c2:num. !c3:num. !c5:num.
        nthUglyNumber_loop 0 seq c2 c3 c5 = seq) /\
     (!iterations:num. !seq:num list.
      !c2:num. !c3:num. !c5:num.
        nthUglyNumber_loop
          (SUC iterations) seq c2 c3 c5 =
        let step = nextUgly seq c2 c3 c5 in
        let next = FST step in
        let c2' = FST (SND step) in
        let c3' = FST (SND (SND step)) in
        let c5' = SND (SND (SND step)) in
        nthUglyNumber_loop
          iterations
          (APPEND seq (CONS next []))
          c2' c3' c5')`;;

let nthUglyNumber = new_definition
  `nthUglyNumber (n:num) =
     nthUglyNumber_get (n - 1)
       (nthUglyNumber_loop
          (n - 1) (CONS 1 []) 0 0 0)`;;

let divideOut = define
  `divideOut(n,p) =
     if 1 < p /\ 0 < n /\ n MOD p = 0
     then divideOut(n DIV p,p)
     else n`;;

let isUgly = new_definition
  `isUgly (x:num) =
     if x = 0 then F
     else
       let n1 = divideOut(x,2) in
       let n2 = divideOut(n1,3) in
       let n3 = divideOut(n2,5) in
       n3 = 1`;;

let nthUglyNumber_range =
  new_recursive_definition num_RECURSION
    `(nthUglyNumber_range 0 = []) /\
     (!n:num.
        nthUglyNumber_range (SUC n) =
        APPEND (nthUglyNumber_range n) (CONS n []))`;;

let nthUglyNumber_postcond = new_definition
  `nthUglyNumber_postcond (n:num) (result:num) <=>
     isUgly result /\
     LENGTH
       (FILTER isUgly (nthUglyNumber_range result)) =
       n - 1`;;

let nthUglyNumber_spec_satisfied =
  `!n:num.
     nthUglyNumber_precond n
     ==> nthUglyNumber_postcond n (nthUglyNumber n)`;;
