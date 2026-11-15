(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2009_a1:
  the zero-sum condition on a real-valued function at the vertices of every
  nondegenerate square forces the function to vanish on the plane, so the
  answer is affirmative. This file contains no proof.
*)

open HolKernel Parse boolLib;
open pairTheory realTheory;

val putnam_2009_a1 =
  ``((!f : (real # real) -> real.
       (!A v : real # real.
          v <> (0, 0)
          ==>
          f A +
          f (FST A + FST v, SND A + SND v) +
          f (FST A + FST v - SND v, SND A + SND v + FST v) +
          f (FST A - SND v, SND A + FST v) = 0)
       ==>
       !P : real # real. f P = 0)
    <=> T)``;
