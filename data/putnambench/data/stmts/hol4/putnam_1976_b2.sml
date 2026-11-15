(*
  Statement-only formalization of PutnamBench artifact putnam_1976_b2:
  a two-generator group with the given relations has exactly eight squares,
  represented by the identity, A^2, and the powers B through B^6. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory listTheory pairTheory pred_setTheory
     groupTheory;

val putnam_1976_b2 =
  ``let int_pow =
      \(g : 'a group) (x : 'a) (n : int).
        if 0 <= n then g.exp x (Num n)
        else g.exp (g.inv x) (Num (-n))
    in
    let word =
      \(g : 'a group) (A B : 'a) (w : (int # int) list).
        FOLDR
          (\t acc.
             g.op
               (g.op
                 (int_pow g A (FST t))
                 (int_pow g B (SND t)))
               acc)
          g.id
          w
    in
      !(g : 'a group) (A B : 'a).
        Group g /\
        A IN g.carrier /\
        B IN g.carrier /\
        g.exp A 4 = g.id /\
        g.exp A 2 <> g.id /\
        g.exp B 7 = g.id /\
        B <> g.id /\
        g.op (g.op (g.op A B) (g.inv A)) B = g.id /\
        (!x : 'a.
           x IN g.carrier
           ==>
           ?w : (int # int) list.
             x = word g A B w)
        ==>
        let S =
          {x : 'a |
             x IN g.carrier /\
             ?C : 'a.
               C IN g.carrier /\
               g.exp C 2 = x}
        in
          CARD S = 8 /\
          S =
            {word g A B [(0, 0)];
             word g A B [(2, 0)];
             word g A B [(0, 1)];
             word g A B [(0, 2)];
             word g A B [(0, 3)];
             word g A B [(0, 4)];
             word g A B [(0, 5)];
             word g A B [(0, 6)]}``;
