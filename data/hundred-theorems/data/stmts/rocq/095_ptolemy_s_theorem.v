From HighSchoolGeometry Require Export triangles_semblables.
From HighSchoolGeometry Require Export orientation.

(* Main proof of Ptolemy's theorem *)

Lemma EntreDeuxVec_sym :
forall (A B C M N :PO),
         vecEntreDeuxVec A B C M -> A<>N->
         cons_AV ( vec A B) (vec A M) = cons_AV (vec A N) (vec A C) ->
         vecEntreDeuxVec A B C N.
Proof.
Admitted.

Lemma EntreDeuxPoint :
forall ( A B M :PO),
          positifColineaire A B M -> positifColineaire B A M -> distance A B = distance A M + distance M B.
Proof.
Admitted.

From HighSchoolGeometry Require Export Droite_espace.


Lemma Exists_Intersection1 : (* on peut prouver grace au lemme
droites_non_paralleles *)
forall (A B C D :PO),
          vecEntreDeuxVec A B C D ->
          exists E :PO, alignes A D E /\ alignes B C E.
Proof.
Admitted.


Lemma  angles_representants_unitaires_r :
(*consequence de l'axiom angles_representants_unitaires *)
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    cons_AV (vec A B) (vec C D) =
    cons_AV  (vec A B)
      (representant_unitaire (vec C D)).
Proof.
Admitted.

Lemma  angles_representants_unitaires2 :
(*consequence de l'axiom angles_representants_unitaires *)
    forall A B C D E F : PO,
    A <> B ->
    C <> D ->
    cons_AV (vec A B) (vec C D) =
    cons_AV (representant_unitaire (vec A B)) (vec C D).
Proof.
Admitted.


Lemma Exists_Intersection :
forall (A B C D :PO),
          vecEntreDeuxVec A B C D ->
          exists E :PO, cons_AV ( vec A B) (vec A E) = cons_AV (vec A D) (vec A C)
                               /\  positifColineaire B C E /\ positifColineaire C B E.
Proof.
Admitted.

Ltac deroule_sont_cocycliques :=
  match goal with H : sont_cocycliques ?A ?B ?C ?D|- _ =>
  generalize H ; let name := fresh in intros name  ;
  unfold sont_cocycliques in name;
  destruct name ;decompose [and] name; clear name;
 repeat match goal with H' : circonscrit ?O ?A ?B ?C  |- _ =>
  unfold circonscrit  in H';
  decompose [and] H' ; clear H' end ;
 repeat match goal with H' : isocele ?O ?A ?B  |- _ =>
  unfold isocele  in H'
  end
end.

Lemma sont_cocycliques_avec_ordre_cycle:
forall (A B C D :PO),
         sont_cocycliques A B C D ->sont_cocycliques B C D A.
Proof.
Admitted.

Lemma sont_cocycliques_avec_ordre_permute:
forall (A B C D :PO),
         sont_cocycliques A B C D ->sont_cocycliques A B D C.
Proof.
Admitted.


Theorem Ptolemee:
forall (A B C D : PO),
         orient A B C -> orient A B D -> orient C D A -> orient C D B ->
         sont_cocycliques A B C D ->
         (distance A B  * distance C D ) + (distance B C *distance D A) =
              distance A C  * distance B D.
Proof.
Admitted.
