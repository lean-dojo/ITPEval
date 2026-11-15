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


From HighSchoolGeometry Require Export repere_ortho_plan.
Set Implicit Arguments.
Unset Strict Implicit.
Parameter AV : Type.
Parameter cons_AV : PP -> PP -> AV.
Parameter plus : AV -> AV -> AV.
Parameter opp : AV -> AV.
 
Axiom
  existence_AB_unitaire : exists A : PO, (exists B : PO, distance A B = 1).
(* Tout angle a un représentant non unique parmi les angles orientés de vecteurs unitaires*)
 
Axiom
  existence_representant_cons :
    forall (a : AV) (A B C : PO),
    distance A B = 1 ->
    exists D : PO, distance C D = 1 /\ a = cons_AV (vec A B) (vec C D).
(* Tout angle orienté de vecteurs non nuls est égal à l'angle orienté des vecteurs unitaires correspondants*)
 
Axiom
  angles_representants_unitaires :
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    cons_AV (vec A B) (vec C D) =
    cons_AV (representant_unitaire (vec A B))
      (representant_unitaire (vec C D)).
 
Axiom
  Chasles :
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    E <> F ->
    plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec C D) (vec E F)) =
    cons_AV (vec A B) (vec E F).
 
Axiom
  def_opp :
    forall A B C D : PO,
    A <> B ->
    C <> D -> opp (cons_AV (vec A B) (vec C D)) = cons_AV (vec C D) (vec A B).
Parameter AV0 : AV.
(* Enroulement de R sur le cercle trigonométrique*)
Parameter image_angle : R -> AV.
 
Axiom AV0_zero : AV0 = image_angle 0.
 
Axiom
  unicite_representant_angle_nul :
    forall A B C : PO,
    distance A B = 1 ->
    distance A C = 1 -> cons_AV (vec A B) (vec A C) = image_angle 0 -> C = B.
 
Axiom
  tout_angle_a_une_mesure :
    forall A B C D : PO,
    A <> B :>PO ->
    C <> D :>PO ->
    exists x : R, image_angle x = cons_AV (vec A B) (vec C D) :>AV.
(* Compatibilité des opérations *)
 
Axiom
  add_mes_compatible :
    forall x y : R,
    image_angle (x + y) = plus (image_angle x) (image_angle y).
 
Axiom mes_opp : forall x : R, image_angle (- x) = opp (image_angle x).
(* Cas particuliers : angles plats et angles droits*)
Parameter pisurdeux : R.
 
Definition pi := pisurdeux + pisurdeux.
 
Definition deuxpi := pi + pi.
 
Axiom
  angle_plat :
    forall A B : PO, A <> B -> image_angle pi = cons_AV (vec A B) (vec B A).
 
Axiom
  pisurdeux_droit :
    forall A B C : PO,
    image_angle pisurdeux = cons_AV (vec A B) (vec A C) ->
    orthogonal (vec A B) (vec A C).
 
Axiom
  droit_direct_ou_indirect :
    forall A B C : PO,
    A <> B ->
    A <> C ->
    orthogonal (vec A B) (vec A C) ->
    image_angle pisurdeux = cons_AV (vec A B) (vec A C) \/
    image_angle (- pisurdeux) = cons_AV (vec A B) (vec A C).
 
Lemma existence_representant_angle :
 forall (A B C : PO) (x : R),
 distance A B = 1 ->
 exists D : PO,
   distance C D = 1 /\ image_angle x = cons_AV (vec A B) (vec C D).
Proof.
Admitted.
 
Lemma tout_angle_mesure : forall a : AV, exists x : R, a = image_angle x :>AV.
Proof.
Admitted.
#[export] Hint Resolve mes_opp add_mes_compatible: geo.
 
Ltac mes a :=
  elim (tout_angle_mesure a); intros;
   match goal with
   | h:(a = image_angle ?X1) |- _ =>
       try rewrite h; repeat rewrite <- mes_opp;
        repeat rewrite <- add_mes_compatible; repeat rewrite <- mes_opp
   end.
#[export] Hint Resolve def_opp Chasles angles_representants_unitaires: geo.
 
Ltac mesure A B C D :=
  elim (tout_angle_a_une_mesure (A:=A) (B:=B) (C:=C) (D:=D)); auto with geo;
   intros;
   match goal with
   | h:(image_angle ?X1 = cons_AV (vec A B) (vec C D)) |- _ =>
       try rewrite <- h; repeat rewrite <- mes_opp;
        repeat rewrite <- add_mes_compatible; repeat rewrite <- mes_opp
   end.
 
Lemma plus_commutative : forall a b : AV, plus a b = plus b a :>AV.
Proof.
Admitted.
 
Lemma plus_angle_zero : forall a : AV, plus a (image_angle 0) = a.
Proof.
Admitted.
 
Lemma plus_associative :
 forall a b c : AV, plus a (plus b c) = plus (plus a b) c :>AV.
Proof.
Admitted.
#[export] Hint Resolve plus_angle_zero: geo.
 
Lemma opp_angle :
 forall a b : AV, plus a b = image_angle 0 :>AV -> b = opp a :>AV.
Proof.
Admitted.
 
Lemma plus_angle_oppose : forall a : AV, plus a (opp a) = image_angle 0.
Proof.
Admitted.
 
Lemma mes_oppx :
 forall (A B C D : PO) (x : R),
 A <> B ->
 C <> D ->
 image_angle x = cons_AV (vec A B) (vec C D) ->
 image_angle (- x) = cons_AV (vec C D) (vec A B).
Proof.
Admitted.
 
Lemma mes_opp_opp :
 forall (A B C D E F G I : PO) (a b : R),
 A <> B ->
 C <> D ->
 E <> F ->
 G <> I ->
 image_angle a = cons_AV (vec A B) (vec C D) ->
 image_angle b = cons_AV (vec E F) (vec G I) ->
 image_angle b = image_angle (- a) ->
 cons_AV (vec E F) (vec G I) = opp (cons_AV (vec A B) (vec C D)).
Proof.
Admitted.
 
Lemma permute_angles :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 cons_AV (vec A B) (vec C D) = cons_AV (vec E F) (vec G I) :>AV ->
 cons_AV (vec C D) (vec A B) = cons_AV (vec G I) (vec E F) :>AV.
Proof.
Admitted.
#[export] Hint Resolve permute_angles: geo.
 
Lemma opp_plus_plus_opp :
 forall A B C D E F G I : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 G <> I :>PO ->
 opp (plus (cons_AV (vec A B) (vec C D)) (cons_AV (vec E F) (vec G I))) =
 plus (opp (cons_AV (vec A B) (vec C D))) (opp (cons_AV (vec E F) (vec G I)))
 :>AV.
Proof.
Admitted.
#[export] Hint Resolve opp_plus_plus_opp: geo.
 
Lemma Chasles_diff :
 forall A B C D E F : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 E <> F :>PO ->
 plus (cons_AV (vec A B) (vec C D)) (opp (cons_AV (vec A B) (vec E F))) =
 cons_AV (vec E F) (vec C D) :>AV.
Proof.
Admitted.
#[export] Hint Resolve pisurdeux_droit: geo.
 
Lemma pisurdeux_scalaire_nul :
 forall A B C : PO,
 image_angle pisurdeux = cons_AV (vec A B) (vec A C) ->
 scalaire (vec A B) (vec A C) = 0.
Proof.
Admitted.
#[export] Hint Resolve pisurdeux_scalaire_nul: geo.
 
Lemma orthogonal_pisurdeux_or :
 forall A B C D : PO,
 A <> B ->
 C <> D ->
 orthogonal (vec A B) (vec C D) ->
 image_angle pisurdeux = cons_AV (vec A B) (vec C D) \/
 image_angle (- pisurdeux) = cons_AV (vec A B) (vec C D).
Proof.
Admitted.
 
Lemma angle_nul :
 forall A B : PO, A <> B -> image_angle 0 = cons_AV (vec A B) (vec A B).
Proof.
Admitted.
 
Lemma pi_plus_pi : image_angle deuxpi = image_angle 0.
Proof.
Admitted.
 
Lemma mesure_mod_deuxpi :
 forall (x : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 image_angle x = cons_AV (vec A B) (vec C D) ->
 image_angle (x + deuxpi) = cons_AV (vec A B) (vec C D).
Proof.
Admitted.
 
Lemma angle_oppu_oppv :
 forall A B C D : PO,
 A <> B :>PO ->
 C <> D :>PO ->
 cons_AV (vec B A) (vec D C) = cons_AV (vec A B) (vec C D) :>AV.
Proof.
Admitted.
#[export] Hint Resolve angle_oppu_oppv: geo.
 
Theorem somme_triangle :
 forall A B C : PO,
 A <> B :>PO ->
 A <> C :>PO ->
 B <> C :>PO ->
 plus (cons_AV (vec A B) (vec A C))
   (plus (cons_AV (vec B C) (vec B A)) (cons_AV (vec C A) (vec C B))) =
 image_angle pi :>AV.
Proof.
Admitted.
 
Lemma angle_triangle :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 B <> C ->
 plus (image_angle pi)
   (opp (plus (cons_AV (vec A B) (vec A C)) (cons_AV (vec B C) (vec B A)))) =
 cons_AV (vec C A) (vec C B).
Proof.
Admitted.
#[export] Hint Resolve angle_triangle: geo.
 
Lemma angles_complementaires_triangle_rectangle :
 forall (A B C : PO) (a : R),
 A <> B ->
 A <> C ->
 B <> C ->
 orthogonal (vec B A) (vec B C) ->
 image_angle a = cons_AV (vec A B) (vec A C) ->
 image_angle (pisurdeux + - a) = cons_AV (vec C A) (vec C B) \/
 image_angle (- pisurdeux + - a) = cons_AV (vec C A) (vec C B).
Proof.
Admitted.
 
Lemma angle_produit_positif_r :
 forall (k : R) (A B C D E : PO),
 A <> B :>PO ->
 D <> E :>PO ->
 k > 0 ->
 vec A C = mult_PP k (vec A B) :>PP ->
 cons_AV (vec D E) (vec A C) = cons_AV (vec D E) (vec A B).
Proof.
Admitted.
#[export] Hint Resolve angles_representants_unitaires: geo.
 
Lemma angle_produit_negatif_r :
 forall (k : R) (A B C D E : PO),
 A <> B ->
 D <> E ->
 k < 0 ->
 vec A C = mult_PP k (vec A B) ->
 cons_AV (vec D E) (vec A C) =
 plus (cons_AV (vec D E) (vec A B)) (image_angle pi).
Proof.
Admitted.
 
Lemma angle_produit_negatif_r2 :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k < 0 ->
 cons_AV (vec C D) (mult_PP k (vec A B)) =
 plus (cons_AV (vec C D) (vec A B)) (image_angle pi).
Proof.
Admitted.
 
Lemma angle_produit_negatif_l :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k < 0 ->
 cons_AV (mult_PP k (vec A B)) (vec C D) =
 plus (cons_AV (vec A B) (vec C D)) (image_angle pi).
Proof.
Admitted.
 
Lemma angle_produit_positif_r2 :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k > 0 ->
 cons_AV (vec C D) (mult_PP k (vec A B)) = cons_AV (vec C D) (vec A B).
Proof.
Admitted.
 
Lemma angle_produit_positif_l :
 forall (k : R) (A B C D : PO),
 A <> B ->
 C <> D ->
 k > 0 ->
 cons_AV (mult_PP k (vec A B)) (vec C D) = cons_AV (vec A B) (vec C D).
Proof.
Admitted.
 
Lemma angle_nul_positif_colineaire :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle 0 ->
 exists k : R, k > 0 /\ vec A C = mult_PP k (vec A B).
Proof.
Admitted.
 
Lemma angles_milieu :
 forall A B C I : PO,
 B <> C :>PO ->
 B <> A :>PO ->
 I = milieu B C :>PO ->
 cons_AV (vec B C) (vec B A) = cons_AV (vec B I) (vec B A) :>AV.
Proof.
Admitted.
 
Lemma angles_milieu2 :
 forall A B C I : PO,
 B <> C :>PO ->
 C <> A :>PO ->
 I = milieu B C :>PO ->
 cons_AV (vec C A) (vec C B) = cons_AV (vec C A) (vec C I) :>AV.
Proof.
Admitted.
 
Lemma milieu_angles :
 forall A B M N : PO,
 A <> B ->
 M <> N ->
 M = milieu A B ->
 cons_AV (vec M A) (vec M N) =
 plus (cons_AV (vec M B) (vec M N)) (image_angle pi) :>AV.
Proof.
Admitted.
 
Axiom
  milieu_angles_orthogonaux :
    forall A B M N : PO,
    A <> B ->
    M <> N ->
    M = milieu A B ->
    orthogonal (vec A B) (vec M N) ->
    cons_AV (vec M A) (vec M N) = cons_AV (vec M N) (vec M B) :>AV.
 
Lemma alignes_distance_positif_colineaire :
 forall (k : R) (A B C : PO),
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle 0 ->
 distance A C = k * distance A B -> vec A C = mult_PP k (vec A B).
Proof.
Admitted.
 
Lemma angle_pi_negatif_colineaire :
 forall A B C : PO,
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle pi ->
 exists k : R, k < 0 /\ vec A C = mult_PP k (vec A B).
Proof.
Admitted.
 
Lemma alignes_distance_negatif_colineaire :
 forall (k : R) (A B C : PO),
 A <> B ->
 A <> C ->
 cons_AV (vec A B) (vec A C) = image_angle pi ->
 distance A C = k * distance A B -> vec A C = mult_PP (- k) (vec A B).
Proof.
Admitted.
#[export] Hint Resolve plus_angle_zero: geo.
