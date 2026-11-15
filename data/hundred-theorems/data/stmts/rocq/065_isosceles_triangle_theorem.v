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


From HighSchoolGeometry Require Export mediatrice.
Set Implicit Arguments.
Unset Strict Implicit.
 
Definition isocele (A B C : PO) : Prop := distance A B = distance A C.
 
Lemma isocele_permute : forall A B C : PO, isocele A B C -> isocele A C B.
Proof.
Admitted.
#[export] Hint Immediate isocele_permute: geo.
 
Lemma isocele_mediatrice :
 forall A B C : PO, isocele A B C -> mediatrice B C A.
Proof.
Admitted.
 
Lemma mediatrice_isocele :
 forall A B C : PO, mediatrice B C A -> isocele A B C.
Proof.
Admitted.
 
Lemma mediane_hauteur_isocele :
 forall A B C I : PO,
 I = milieu B C -> orthogonal (vec B C) (vec I A) -> isocele A B C.
Proof.
Admitted.
 
Lemma mediane_isocele_hauteur :
 forall A B C I : PO,
 I = milieu B C -> isocele A B C -> orthogonal (vec I A) (vec B C).
Proof.
Admitted.
 
Lemma hauteur_isocele_mediane :
 forall A B C I : PO,
 B <> C ->
 orthogonal (vec B C) (vec I A) ->
 isocele A B C -> alignes B C I -> I = milieu B C.
Proof.
Admitted.
 
Lemma isocele_mediane_bissectrice :
 forall A B C I : PO,
 A <> I ->
 B <> C ->
 I = milieu B C ->
 isocele A B C -> cons_AV (vec A B) (vec A I) = cons_AV (vec A I) (vec A C).
Proof.
Admitted.
 
Lemma isocele_angles_base :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 isocele A B C -> cons_AV (vec B C) (vec B A) = cons_AV (vec C A) (vec C B).
Proof.
Admitted.
 
Lemma diametre_rectangle :
 forall A B C C' : PO,
 A <> B ->
 C' = milieu A B ->
 distance C' C = distance C' A -> orthogonal (vec C A) (vec C B).
Proof.
Admitted.
