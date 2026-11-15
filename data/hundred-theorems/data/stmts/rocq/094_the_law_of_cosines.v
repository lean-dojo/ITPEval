(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


From HighSchoolGeometry Require Export euclidien_classiques.
From HighSchoolGeometry Require Export trigo.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma produit_scalaire_Cosinus :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 scalaire (vec A B) (vec A C) =
 distance A B * (distance A C * Cos (cons_AV (vec A B) (vec A C))).
Proof.
Admitted.
 
Lemma produit_scalaire_cosinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 scalaire (vec A B) (vec A C) = distance A B * (distance A C * cos a).
Proof.
Admitted.
#[export] Hint Resolve carre_scalaire_distance: geo.
 
Lemma triangle_rectangle_Cos :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 orthogonal (vec B A) (vec B C) ->
 distance A B = distance A C * Cos (cons_AV (vec A B) (vec A C)).
Proof.
Admitted.
 
Lemma triangle_rectangle_cos :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance A B = distance A C * cos a.
Proof.
Admitted.
 
Lemma triangle_rectangle_absolu_cos :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance A B = distance A C * Rabs (cos a).
Proof.
Admitted.
 
Lemma orthogonal_distincts :
 forall A B C : PO,
 A <> B -> A <> C -> orthogonal (vec A B) (vec A C) -> B <> C.
Proof.
Admitted.
 
Lemma triangle_rectangle_direct_sinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle pisurdeux = cons_AV (vec B C) (vec B A) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C B = distance C A * sin a.
Proof.
Admitted.
 
Lemma triangle_rectangle_indirect_sinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle (- pisurdeux) = cons_AV (vec B C) (vec B A) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C B = distance C A * - sin a.
Proof.
Admitted.
 
Lemma triangle_rectangle_absolu_sinus :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C B = distance C A * Rabs (sin a).
Proof.
Admitted.
 
Lemma triangle_rectangle_direct_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle pisurdeux = cons_AV (vec B C) (vec B A) ->
 distance C B = distance C A * Sin (cons_AV (vec A B) (vec A C)).
Proof.
Admitted.
 
Lemma triangle_rectangle_indirect_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 image_angle (- pisurdeux) = cons_AV (vec B C) (vec B A) ->
 distance C B = distance C A * - Sin (cons_AV (vec A B) (vec A C)).
Proof.
Admitted.
 
Lemma triangle_rectangle_absolu_Sin :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 orthogonal (vec B A) (vec B C) ->
 distance C B = distance C A * Rabs (Sin (cons_AV (vec A B) (vec A C))).
Proof.
Admitted.
 
Lemma projete_negatif_cos :
 forall (A B C H : PO) (a k : R),
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 vec A H = mult_PP k (vec A B) ->
 k < 0 -> image_angle a = cons_AV (vec A B) (vec A C) -> cos a < 0.
Proof.
Admitted.
 
Lemma projete_absolu_cos :
 forall (A B C H : PO) (a : R),
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance A H = distance A C * Rabs (cos a).
Proof.
Admitted.
 
Lemma projete_absolu_sin :
 forall (A B C H : PO) (a : R),
 triangle A B C ->
 H = projete_orthogonal A B C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 distance C H = distance C A * Rabs (sin a).
Proof.
Admitted.
 
Lemma projete_absolu_Sin :
 forall A B C H : PO,
 triangle A B C ->
 H = projete_orthogonal A B C ->
 distance C H = distance C A * Rabs (Sin (cons_AV (vec A B) (vec A C))).
Proof.
Admitted.
 
Lemma projete_absolu_Cos :
 forall A B C H : PO,
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 distance A H = distance A C * Rabs (Cos (cons_AV (vec A B) (vec A C))).
Proof.
Admitted.
 
Theorem Al_Kashi_Cos :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 Rsqr (distance B C) =
 Rsqr (distance A B) + Rsqr (distance A C) +
 - (2 * (distance A B * (distance A C * Cos (cons_AV (vec A B) (vec A C))))).
Proof.
Admitted.
 
Theorem Al_Kashi :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 Rsqr (distance B C) =
 Rsqr (distance A B) + Rsqr (distance A C) +
 - (2 * (distance A B * (distance A C * cos a))).
Proof.
Admitted.
 
Lemma triangles_isometriques :
 forall (A B C A' B' C' : PO) (x x' y y' : R),
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B ->
 distance A' C' = distance A C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV ->
 image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
 image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
 image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
 image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
 distance B' C' = distance B C /\ cos x = cos x' /\ cos y = cos y'.
Proof.
Admitted.
 
Axiom
  angles_egaux_triangle :
    forall (A B C A' B' C' : PO) (x x' y y' : R),
    A <> B :>PO ->
    A <> C :>PO ->
    B <> C :>PO ->
    cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV ->
    image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
    image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
    image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
    image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
    cos x = cos x' ->
    cos y = cos y' ->
    cons_AV (vec B C) (vec B A) = cons_AV (vec B' C') (vec B' A') :>AV /\
    cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
 
Lemma cas_egalite_triangle :
 forall A B C A' B' C' : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B ->
 distance A' C' = distance A C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' B') (vec A' C') :>AV ->
 distance B' C' = distance B C /\
 cons_AV (vec B C) (vec B A) = cons_AV (vec B' C') (vec B' A') :>AV /\
 cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
Proof.
Admitted.
 
Lemma triangles_isometriques_indirects :
 forall (A B C A' B' C' : PO) (x x' y y' : R),
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B ->
 distance A' C' = distance A C ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' C') (vec A' B') :>AV ->
 image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
 image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
 image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
 image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
 distance B' C' = distance B C /\ cos x = cos x' /\ cos y = cos y'.
Proof.
Admitted.
 
Axiom
  angles_egaux_triangle_indirect :
    forall (A B C A' B' C' : PO) (x x' y y' : R),
    A <> B :>PO ->
    A <> C :>PO ->
    B <> C :>PO ->
    cons_AV (vec A B) (vec A C) = cons_AV (vec A' C') (vec A' B') :>AV ->
    image_angle x = cons_AV (vec B C) (vec B A) :>AV ->
    image_angle x' = cons_AV (vec B' C') (vec B' A') :>AV ->
    image_angle y = cons_AV (vec C A) (vec C B) :>AV ->
    image_angle y' = cons_AV (vec C' A') (vec C' B') :>AV ->
    cos x = cos x' :>R ->
    cos y = cos y' :>R ->
    cons_AV (vec B C) (vec B A) = cons_AV (vec B' A') (vec B' C') :>AV /\
    cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
 
Lemma cas_egalite_triangle_indirect :
 forall A B C A' B' C' : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 distance A' B' = distance A B :>R ->
 distance A' C' = distance A C :>R ->
 cons_AV (vec A B) (vec A C) = cons_AV (vec A' C') (vec A' B') :>AV ->
 distance B' C' = distance B C :>R /\
 cons_AV (vec B C) (vec B A) = cons_AV (vec B' A') (vec B' C') :>AV /\
 cons_AV (vec C A) (vec C B) = cons_AV (vec C' A') (vec C' B') :>AV.
Proof.
Admitted.
