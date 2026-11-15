(*
  Statement-only formalization of "The Number of Platonic Solids" from Hundred
  Theorems artifact 050. A full-dimensional real three-dimensional polytope
  with m edges on every facet and n incident edges at every vertex exists
  exactly for the five Platonic incidence pairs. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory cardinalTheory pairTheory pred_setTheory realTheory;

val number_of_platonic_solids =
  ``let xcoord =
      \p : (real # real) # real. FST (FST p)
    in
    let ycoord =
      \p : (real # real) # real. SND (FST p)
    in
    let zcoord =
      \p : (real # real) # real. SND p
    in
    let plane_value =
      \(h : (real # real) # (real # real))
       (p : (real # real) # real).
        FST (FST h) * xcoord p +
        SND (FST h) * ycoord p +
        FST (SND h) * zcoord p
    in
    let plane_rhs =
      \h : (real # real) # (real # real). SND (SND h)
    in
    let nonzero_normal =
      \h : (real # real) # (real # real).
        ~(FST (FST h) = 0 /\
          SND (FST h) = 0 /\
          FST (SND h) = 0)
    in
    let bounded3 =
      \P : (((real # real) # real) set).
        ?B : real.
          0 < B /\
          !p.
            p IN P ==>
            abs (xcoord p) <= B /\
            abs (ycoord p) <= B /\
            abs (zcoord p) <= B
    in
    let full_dimensional3 =
      \P : (((real # real) # real) set).
        ?c r.
          0 < r /\
          !p.
            (xcoord p - xcoord c) * (xcoord p - xcoord c) +
            (ycoord p - ycoord c) * (ycoord p - ycoord c) +
            (zcoord p - zcoord c) * (zcoord p - zcoord c) < r * r
            ==> p IN P
    in
    let polytope3 =
      \P : (((real # real) # real) set).
        ?H : (((real # real) # (real # real)) set).
          FINITE H /\
          (!h. h IN H ==> nonzero_normal h) /\
          (!p.
             p IN P <=>
             !h. h IN H ==> plane_value h p <= plane_rhs h) /\
          bounded3 P /\
          full_dimensional3 P
    in
    let face_of =
      \(f : (((real # real) # real) set))
       (P : (((real # real) # real) set)).
        ~(f = EMPTY) /\
        f SUBSET P /\
        ?h : (real # real) # (real # real).
          nonzero_normal h /\
          (!p. p IN P ==> plane_value h p <= plane_rhs h) /\
          f = {p | p IN P /\ plane_value h p = plane_rhs h}
    in
    let on_line =
      \(p : (real # real) # real)
       (q : (real # real) # real)
       (s : (real # real) # real).
        ?t : real.
          xcoord s = xcoord p + t * (xcoord q - xcoord p) /\
          ycoord s = ycoord p + t * (ycoord q - ycoord p) /\
          zcoord s = zcoord p + t * (zcoord q - zcoord p)
    in
    let on_plane =
      \(p : (real # real) # real)
       (q : (real # real) # real)
       (r : (real # real) # real)
       (s : (real # real) # real).
        ?u v : real.
          xcoord s =
            xcoord p +
            u * (xcoord q - xcoord p) +
            v * (xcoord r - xcoord p) /\
          ycoord s =
            ycoord p +
            u * (ycoord q - ycoord p) +
            v * (ycoord r - ycoord p) /\
          zcoord s =
            zcoord p +
            u * (zcoord q - zcoord p) +
            v * (zcoord r - zcoord p)
    in
    let dimension0 =
      \f : (((real # real) # real) set).
        ?p. f = {p}
    in
    let dimension1 =
      \f : (((real # real) # real) set).
        ?p q.
          p IN f /\
          q IN f /\
          ~(p = q) /\
          !s. s IN f ==> on_line p q s
    in
    let dimension2 =
      \f : (((real # real) # real) set).
        ?p q r.
          p IN f /\
          q IN f /\
          r IN f /\
          ~(p = q) /\
          ~on_line p q r /\
          !s. s IN f ==> on_plane p q r s
    in
      !(m : num) (n : num).
        (?P : (((real # real) # real) set).
          polytope3 P /\
          (!f.
            face_of f P /\ dimension2 f ==>
            CARD {e | face_of e P /\ dimension1 e /\ e SUBSET f} = m) /\
          (!v.
            face_of v P /\ dimension0 v ==>
            CARD {e | face_of e P /\ dimension1 e /\ v SUBSET e} = n))
        <=>
        (m = 3 /\ n = 3) \/
        (m = 4 /\ n = 3) \/
        (m = 3 /\ n = 4) \/
        (m = 5 /\ n = 3) \/
        (m = 3 /\ n = 5)``;
