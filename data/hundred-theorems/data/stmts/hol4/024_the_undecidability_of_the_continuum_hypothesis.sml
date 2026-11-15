(*
  Statement-only formalization of "The Undecidability of the Continuum Hypothesis" from Hundred
  Theorems item 024. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory cardinalTheory combinTheory pred_setTheory;

val extensions_of_ctms =
  ``let pair_num =
      \i j : num. ((i + j) * (i + j + 1)) DIV 2 + j
    in
    let valuation =
      \(M : (num set) set) (v : num -> num set).
        !i. v i IN M
    in
    let denumerable =
      \(M : (num set) set).
        ?enumerate : num -> num set.
          BIJ enumerate (UNIV : num set) M
    in
    let transitive_model =
      \(mem : num set -> num set -> bool) (M : (num set) set).
        (!x y. y IN M /\ mem x y ==> x IN M) /\
        (!S : (num set) set.
           S SUBSET M /\ ~(S = EMPTY) ==>
           ?x. x IN S /\ !y. y IN S ==> ~mem y x)
    in
    let tarski =
      \(mem : num set -> num set -> bool)
       (M : (num set) set)
       (sat : (num -> num set) -> num -> bool).
        (!v i j.
           valuation M v ==>
           (sat v (5 * pair_num i j) <=> v i = v j)) /\
        (!v i j.
           valuation M v ==>
           (sat v (5 * pair_num i j + 1) <=> mem (v i) (v j))) /\
        (!v p.
           valuation M v ==>
           (sat v (5 * p + 2) <=> ~sat v p)) /\
        (!v p q.
           valuation M v ==>
           (sat v (5 * pair_num p q + 3) <=>
              sat v p /\ sat v q)) /\
        (!v i p.
           valuation M v ==>
           (sat v (5 * pair_num i p + 4) <=>
              ?x. x IN M /\ sat ((i =+ x) v) p))
    in
    let zf_model =
      \(mem : num set -> num set -> bool)
       (M : (num set) set)
       (sat : (num -> num set) -> num -> bool).
        tarski mem M sat /\
        (!x y.
           x IN M /\ y IN M /\
           (!z. z IN M ==> (mem z x <=> mem z y))
           ==> x = y) /\
        (?e. e IN M /\ !z. z IN M ==> ~mem z e) /\
        (!x y.
           x IN M /\ y IN M ==>
           ?p. p IN M /\
               !z. z IN M ==> (mem z p <=> z = x \/ z = y)) /\
        (!a.
           a IN M ==>
           ?u. u IN M /\
               !z. z IN M ==>
                 (mem z u <=>
                    ?y. y IN M /\ mem y a /\ mem z y)) /\
        (!a.
           a IN M ==>
           ?p. p IN M /\
               !z. z IN M ==>
                 (mem z p <=>
                    !w. w IN M /\ mem w z ==> mem w a)) /\
        (?i.
           i IN M /\
           (?e.
              e IN M /\
              (!z. z IN M ==> ~mem z e) /\
              mem e i) /\
           (!x.
              x IN M /\ mem x i ==>
              ?s. s IN M /\
                  (!z.
                     z IN M ==>
                     (mem z s <=> mem z x \/ z = x)) /\
                  mem s i)) /\
        (!a.
           a IN M /\ (?x. x IN M /\ mem x a) ==>
           ?x. x IN M /\ mem x a /\
               !y. y IN M /\ mem y a ==> ~mem y x) /\
        (!phi v a.
           valuation M v /\ a IN M ==>
           ?b. b IN M /\
               !x. x IN M ==>
                 (mem x b <=>
                    mem x a /\ sat ((0 =+ x) v) phi)) /\
        (!phi v a.
           valuation M v /\ a IN M /\
           (!x.
              x IN M /\ mem x a ==>
              ?y. y IN M /\
                  sat ((1 =+ y) ((0 =+ x) v)) phi /\
                  (!y'.
                     y' IN M /\
                     sat ((1 =+ y') ((0 =+ x) v)) phi
                     ==> y' = y))
           ==>
           ?b. b IN M /\
               !y. y IN M ==>
                 (mem y b <=>
                    ?x. x IN M /\ mem x a /\
                        sat ((1 =+ y) ((0 =+ x) v)) phi))
    in
    let singleton =
      \(mem : num set -> num set -> bool)
       (M : (num set) set) x s.
        x IN M /\ s IN M /\
        !z. z IN M ==> (mem z s <=> z = x)
    in
    let unordered_pair =
      \(mem : num set -> num set -> bool)
       (M : (num set) set) x y p.
        x IN M /\ y IN M /\ p IN M /\
        !z. z IN M ==> (mem z p <=> z = x \/ z = y)
    in
    let ordered_pair =
      \(mem : num set -> num set -> bool)
       (M : (num set) set) x y p.
        ?sx xy.
          singleton mem M x sx /\
          unordered_pair mem M x y xy /\
          unordered_pair mem M sx xy p
    in
    let relates =
      \(mem : num set -> num set -> bool)
       (M : (num set) set) f x y.
        ?p. p IN M /\ ordered_pair mem M x y p /\ mem p f
    in
    let choice_function =
      \(mem : num set -> num set -> bool)
       (M : (num set) set) a f.
        a IN M /\ f IN M /\
        (!p.
           p IN M /\ mem p f ==>
           ?x y.
             x IN M /\ y IN M /\ mem x a /\ mem y x /\
             ordered_pair mem M x y p) /\
        (!x.
           x IN M /\ mem x a ==>
           ?y. y IN M /\ mem y x /\ relates mem M f x y) /\
        (!x y z.
           x IN M /\ y IN M /\ z IN M /\
           relates mem M f x y /\ relates mem M f x z
           ==> y = z)
    in
    let ac_model =
      \(mem : num set -> num set -> bool) (M : (num set) set).
        !a.
          a IN M /\
          (!x.
             x IN M /\ mem x a ==>
             ?y. y IN M /\ mem y x)
          ==>
          ?f. f IN M /\ choice_function mem M a f
    in
    let transitive_object =
      \(mem : num set -> num set -> bool) (a : num set).
        !x y. mem x y /\ mem y a ==> mem x a
    in
    let ordinal =
      \(mem : num set -> num set -> bool) (a : num set).
        transitive_object mem a /\
        (!x. mem x a ==> transitive_object mem x) /\
        (!x y.
           mem x a /\ mem y a ==>
           x = y \/ mem x y \/ mem y x) /\
        (!S : (num set) set.
           S SUBSET {x | mem x a} /\ ~(S = EMPTY) ==>
           ?m. m IN S /\ !x. x IN S ==> ~mem x m)
    in
    let end_extends =
      \(old_mem : num set -> num set -> bool)
       (M : (num set) set)
       (new_mem : num set -> num set -> bool).
        !x y. y IN M ==> (new_mem x y <=> old_mem x y)
    in
    !(mem : num set -> num set -> bool) (M : (num set) set).
      denumerable M /\
      transitive_model mem M /\
      (?satM : (num -> num set) -> num -> bool.
         zf_model mem M satM)
      ==>
      ?memN N satN.
        M SUBSET N /\
        ~(M = N) /\
        end_extends mem M memN /\
        denumerable N /\
        transitive_model memN N /\
        zf_model memN N satN /\
        (!alpha : num set.
           (alpha IN M /\ ordinal mem alpha) <=>
           (alpha IN N /\ ordinal memN alpha)) /\
        (ac_model mem M ==> ac_model memN N)``;
