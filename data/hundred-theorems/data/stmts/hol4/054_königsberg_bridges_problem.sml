(*
  Statement-only formalization of the Hundred Theorems artifact 054,
  "Königsberg Bridges Problem": the seven-bridge multigraph on four
  landmasses has no trail traversing every bridge exactly once. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory pairTheory;

val koenigsberg_bridges_problem =
  ``let termini =
      \e : num.
        if e = 10 then (0, 1)
        else if e = 20 then (0, 2)
        else if e = 30 then (0, 3)
        else if e = 40 then (1, 2)
        else if e = 50 then (1, 2)
        else if e = 60 then (2, 3)
        else if e = 70 then (2, 3)
        else (0, 0)
    in
    let incident =
      \e u v.
        (u = FST (termini e) /\ v = SND (termini e)) \/
        (u = SND (termini e) /\ v = FST (termini e))
    in
      ~(?e0 e1 e2 e3 e4 e5 e6 : num.
          PERM [e0; e1; e2; e3; e4; e5; e6]
               [10; 20; 30; 40; 50; 60; 70] /\
          ?v0 v1 v2 v3 v4 v5 v6 v7 : num.
            incident e0 v0 v1 /\
            incident e1 v1 v2 /\
            incident e2 v2 v3 /\
            incident e3 v3 v4 /\
            incident e4 v4 v5 /\
            incident e5 v5 v6 /\
            incident e6 v6 v7)``;
