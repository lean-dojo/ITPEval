(*
  Statement-only formalization of Hundred Theorems artifact 006, "Gödel's
  Incompleteness Theorem": a weakly consistent arithmetic theory extending NN,
  whose axioms are represented within arithmetic, has a closed formula
  independent of the theory. This file contains no proof.
*)

prioritize_num();;
needs "Library/rstc.ml";;
needs "Library/prime.ml";;
needs "Arithmetic/fol.ml";;
needs "Arithmetic/definability.ml";;
needs "Arithmetic/tarski.ml";;

let GOEDEL_FIRST_INCOMPLETENESS =
  `!thy:form->bool repT:form v0:num.
      {!!0 (Not(Suc(V 0) === Z)),
       !!1 (!!0 (Suc(V 0) === Suc(V 1) --> V 0 === V 1)),
       !!0 (V 0 ++ Z === V 0),
       !!1 (!!0 (V 0 ++ Suc(V 1) === Suc(V 0 ++ V 1))),
       !!0 (V 0 ** Z === Z),
       !!1 (!!0 (V 0 ** Suc(V 1) === V 0 ** V 1 ++ V 0)),
       !!0 (Not(V 0 << Z)),
       !!1 (!!0 (V 0 << Suc(V 1) --> (V 0 << V 1 || V 0 === V 1))),
       !!1 (!!0 (V 0 << V 1 || V 0 === V 1 || V 1 << V 0))}
      SUBSET thy /\
      (!v:num. v IN FV repT ==> v = v0) /\
      (!f:form.
         f IN thy
         ==> thy |-- formsubst (v0 |=> numeral (gform f)) repT) /\
      (!f:form.
         ~(f IN thy)
         ==> thy |-- Not(formsubst (v0 |=> numeral (gform f)) repT)) /\
      (!p:form x:num.
         (!y:num. y IN FV p ==> x = y) /\
         thy |-- ??x (Not p)
         ==> ?n:num. ~(thy |-- formsubst (x |=> numeral n) p))
      ==> ?f:form.
            (~(thy |-- f) /\ ~(thy |-- Not f)) /\
            FV f = EMPTY`;;
