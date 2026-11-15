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


From HighSchoolGeometry Require Export distance_euclidienne.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma carre_scalaire_somme :
 forall A B C D : PO,
 scalaire (add_PP (vec A B) (vec C D)) (add_PP (vec A B) (vec C D)) =
 2 * scalaire (vec A B) (vec C D) +
 (scalaire (vec A B) (vec A B) + scalaire (vec C D) (vec C D)) :>R.
Proof.
Admitted.
 
Lemma difference_Pythagore :
 forall A B C : PO,
 scalaire (vec B C) (vec B C) =
 scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) +
 -2 * scalaire (vec A B) (vec A C) :>R.
Proof.
Admitted.
 
Lemma triangle_Pythagore :
 forall A B C : PO,
 scalaire (vec A B) (vec A C) = 0 <->
 scalaire (vec B C) (vec B C) =
 scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) :>R.
Proof.
Admitted.
 
Theorem Pythagore :
 forall A B C : PO,
 orthogonal (vec A B) (vec A C) <->
 Rsqr (distance B C) = Rsqr (distance A B) + Rsqr (distance A C) :>R.
Proof.
Admitted.
 
Lemma longueur_mediane :
 forall A B C I : PO,
 I = milieu B C ->
 Rsqr (distance A B) + Rsqr (distance A C) =
 R2 * (Rsqr (distance A I) + Rsqr (distance I B)) :>R.
Proof.
Admitted.
 
Lemma demi_longueur :
 forall A B I : PO,
 I = milieu A B -> Rsqr (distance A B) = R4 * Rsqr (distance A I) :>R.
Proof.
Admitted.
 
Theorem mediane :
 forall A B C I : PO,
 I = milieu B C ->
 R4 * Rsqr (distance A I) =
 R2 * (Rsqr (distance A B) + Rsqr (distance A C)) - Rsqr (distance B C) :>R.
Proof.
Admitted.
 
Lemma rectangle_Pythagore :
 forall A B C : PO,
 orthogonal (vec A B) (vec A C) <->
 scalaire (vec B C) (vec B C) =
 scalaire (vec A B) (vec A B) + scalaire (vec A C) (vec A C) :>R.
Proof.
Admitted.
From HighSchoolGeometry Require Export projection_orthogonale.
 
Lemma Pythagore_projete_orthogonal :
 forall A B C H : PO,
 A <> B :>PO ->
 H = projete_orthogonal A B C :>PO ->
 Rsqr (distance A C) = Rsqr (distance H A) + Rsqr (distance H C) :>R /\
 Rsqr (distance B C) = Rsqr (distance H B) + Rsqr (distance H C) :>R.
Proof.
Admitted.
 
Lemma scalaire_difference_carre :
 forall A B I M : PO,
 I = milieu A B ->
 scalaire (vec M A) (vec M B) = Rsqr (distance M I) + - Rsqr (distance I A).
Proof.
Admitted.
 
Lemma egalite_scalaire_deux_projetes :
 forall A B C H K : PO,
 A <> B ->
 A <> C ->
 H = projete_orthogonal A B C ->
 K = projete_orthogonal A C B ->
 scalaire (vec A B) (vec A H) = scalaire (vec A K) (vec A C).
Proof.
Admitted.
 
Lemma projete_distance_Rlt :
 forall A B C H : PO,
 A <> B ->
 H <> B -> H = projete_orthogonal A B C -> distance C H < distance C B.
Proof.
Admitted.
Parameter distance_droite : PO -> DR -> R.
 
Axiom
  distance_droite_def :
    forall A B C H : PO,
    A <> B ->
    H = projete_orthogonal A B C ->
    distance_droite C (droite A B) = distance C H.
 
Lemma existence_distance_droite :
 forall A B C : PO,
 A <> B -> exists d : R, d = distance_droite C (droite A B).
Proof.
Admitted.
