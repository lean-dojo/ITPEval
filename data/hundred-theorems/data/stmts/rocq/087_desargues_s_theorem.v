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


From HighSchoolGeometry Require Export parallelisme_concours.
Set Implicit Arguments.
Unset Strict Implicit.
 
Lemma triangle_droite_milieu_paralleles :
 forall A B C A' B' : PO,
 triangle A B C ->
 A' = milieu B C :>PO ->
 B' = milieu A C :>PO -> paralleles (droite A B) (droite A' B').
Proof.
Admitted.
 
Lemma milieu_parallelogrammme :
 forall A B C D I : PO, vec A B = vec D C -> I = milieu A C -> I = milieu B D.
Proof.
Admitted.
 
Lemma milieu_parallelogrammme_rec:
 forall (A B C D I : PO), I = milieu A C -> I = milieu B D ->  vec A B = vec D C.
Proof.
Admitted.

Lemma caract_milieu_parallelogramme:
 forall (A B C D : PO),  (milieu A C = milieu B D <-> parallelogramme A B C D).
Proof.
Admitted.

Lemma Thales_PP :
 forall A B C D : PO,
 A <> C ->
 B <> D ->
 paralleles (droite A C) (droite B D) ->
 exists k : R,
   add_PP (cons 1 A) (cons k B) = add_PP (cons 1 C) (cons k D) :>PP.
Proof.
Admitted.
 
Lemma reciproque_Thales_PP :
 forall (A B C D : PO) (k : R),
 A <> C :>PO ->
 B <> D :>PO ->
 add_PP (cons 1 A) (cons k B) = add_PP (cons 1 C) (cons k D) ->
 paralleles (droite A C) (droite B D).
Proof.
Admitted.
 
Theorem Thales_expl :
 forall A B C D : PO,
 A <> C :>PO ->
 B <> D :>PO ->
 paralleles (droite A C) (droite B D) ->
 vec B A = vec D C \/
 (exists k : R,
    (exists I : PO,
       vec I A = mult_PP k (vec I B) /\ vec I C = mult_PP k (vec I D))).
Proof.
Admitted.
 
Theorem reciproque_Thales_expl :
 forall (A B C D I : PO) (k : R),
 A <> C :>PO ->
 B <> D :>PO ->
 vec I A = mult_PP k (vec I B) :>PP ->
 vec I C = mult_PP k (vec I D) :>PP -> paralleles (droite A C) (droite B D).
Proof.
Admitted.
 
Lemma trapeze_complet_PP :
 forall A B C D I J : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 I = milieu C D ->
 J = milieu A B ->
 ex
   (fun k : R =>
    add_PP (cons 1 A) (cons k C) = add_PP (cons 1 B) (cons k D) :>PP /\
    add_PP (cons 1 A) (cons k C) = add_PP (cons 1 J) (cons k I) :>PP).
Proof.
Admitted.
 
Lemma trapeze_complet_expl :
 forall A B C D I J : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 I = milieu C D ->
 J = milieu A B ->
 vec C A = vec D B /\ vec C A = vec I J \/ concours_3 A C B D J I.
Proof.
Admitted.
#[export] Hint Immediate paralleles_ABBA paralleles_sym: geo.
 
Lemma trapeze_complet_expl2 :
 forall A B C D I J : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 paralleles (droite A B) (droite C D) ->
 I = milieu C D ->
 J = milieu A B ->
 vec D A = vec C B /\ vec D A = vec I J \/ concours_3 A D B C J I.
Proof.
Admitted.
 
Theorem Desargues :
 forall A B C A1 B1 C1 S : PO,
 C <> C1 ->
 B <> B1 ->
 C <> S ->
 B <> S ->
 C1 <> S ->
 B1 <> S ->
 A1 <> B1 ->
 A1 <> C1 ->
 B <> C ->
 B1 <> C1 ->
 triangle A A1 B ->
 triangle A A1 C ->
 alignes A A1 S ->
 alignes B B1 S ->
 alignes C C1 S ->
 paralleles (droite A B) (droite A1 B1) ->
 paralleles (droite A C) (droite A1 C1) ->
 paralleles (droite B C) (droite B1 C1).
Proof.
Admitted.
 
Lemma Thales_concours :
 forall (k : R) (A B C I J : PO),
 triangle A B C ->
 k <> 0 :>R ->
 vec A I = mult_PP k (vec A B) :>PP ->
 paralleles (droite B C) (droite I J) ->
 alignes A C J -> vec A J = mult_PP k (vec A C) :>PP.
Proof.
Admitted.
 
Lemma reciproque_droite_milieu :
 forall A B C I J : PO,
 triangle A B C ->
 I = milieu A B :>PO ->
 paralleles (droite B C) (droite I J) -> alignes A C J -> J = milieu A C :>PO.
Proof.
Admitted.
