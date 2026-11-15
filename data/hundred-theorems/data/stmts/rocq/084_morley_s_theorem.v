From HighSchoolGeometry Require Export trigo.
Set  Implicit Arguments.
Unset Strict Implicit.
(* Formules de trigonometrie necessaires.*)
 
Lemma prod_sin:
 forall (a b : R),  2 * (sin (a + b) * sin (a - b)) = cos (2 * b) - cos (2 * a).
Proof.
Admitted.
 
Lemma sin_3_a: forall (a : R),  sin (3 * a) = sin a * (2 * cos (2 * a) + 1).
Proof.
Admitted.
 
Lemma Al_Kashi_sin_cos:
 forall (a b c : R),
 (a + b) + c = pi ->
  Rsqr (sin c) = (Rsqr (sin a) + Rsqr (sin b)) - ((2 * sin a) * sin b) * cos c.
Proof.
Admitted.
(* Definition de pisurtrois et formules de trigonometrie.*)
Parameter pisurtrois : R.
 
Axiom pisurtrois_def : 3 * pisurtrois = pi.
 
Axiom sin_pisurtrois_non_zero : sin pisurtrois <> 0.
 
Lemma cos_2_pisurtrois: 2 * cos (2 * pisurtrois) + 1 = 0.
Proof.
Admitted.
 
Lemma sin_3_a_pisurtrois:
 forall (a : R),
  sin (3 * a) = 4 * (sin a * (sin (pisurtrois + a) * sin (pisurtrois - a))).
Proof.
Admitted.
 
Lemma Al_Kashi_pisurtrois:
 forall a b c,
 (a + b) + c = pisurtrois ->
  Rsqr (sin b) =
  (Rsqr (sin (pisurtrois + a)) + Rsqr (sin (pisurtrois + c))) -
  ((2 * sin (pisurtrois + a)) * sin (pisurtrois + c)) * cos b.
Proof.
Admitted.
From HighSchoolGeometry Require Export cocyclicite.
(* lemme a mettre dans distance_euclidienne apres colinearite_distance*)
 
Lemma distance_double_milieu:
 forall (B C A' : PO), A' = milieu B C ->  distance B C = 2 * distance A' C.
Proof.
Admitted.
(* corollaire du theoreme de l'angle inscrit et de l'angle au centre
   on utilise le triangle rectangle forme par un cote et sa mediatrice*)
 
Lemma demi_angle_centre:
 forall (A B C A' O : PO),
 triangle A B C ->
 O <> A' ->
 A' = milieu B C ->
 circonscrit O A B C ->
  double_AV (cons_AV (vec A B) (vec A C)) =
  double_AV (cons_AV (vec O A') (vec O C)).
Proof.
Admitted.
(*deux angles ayant des mesures differant d'un multiple de pi ont des sinus egaux ou opposes*)
 
Axiom
   egalite_double_abs_Sin :
   forall A B C E F G,
   double_AV (cons_AV (vec A B) (vec A C)) =
   double_AV (cons_AV (vec E F) (vec E G)) ->
    Rabs (Sin (cons_AV (vec A B) (vec A C))) =
    Rabs (Sin (cons_AV (vec E F) (vec E G))).

From HighSchoolGeometry Require Export complements_cercle.
(* theoreme : dans un triangle avec les notations habituelles  a = 2 R sin A
   cas particulier : le cote est un diametre du cercle circonscrit*)
 
Lemma diametre_Sinus:
 forall (A B C O : PO),
 triangle A B C ->
 O = milieu B C ->
 circonscrit O A B C ->
  distance B C = 2 * (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C)))).
Proof.
Admitted.
(* cas general*)
 
Lemma rayon_Sinus_general:
 forall (A B C A' O : PO),
 triangle A B C ->
 O <> A' ->
 A' = milieu B C ->
 circonscrit O A B C ->
  distance B C = 2 * (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C)))).
Proof.
Admitted.
(* Ce theoreme montre que dans un triangle  a = 2R sin A  avec les notations habituelles.*)
 
Theorem rayon_Sinus:
 forall A B C O,
 triangle A B C ->
 circonscrit O A B C ->
  distance B C = 2 * (distance O C * Rabs (Sin (cons_AV (vec A B) (vec A C)))).
Proof.
Admitted.
 
Lemma existence_rayon_circonscrit:
 forall A B C,
 triangle A B C ->
  (exists O : PO , circonscrit O A B C /\ (exists r : R , r = distance O C ) ).
Proof.
Admitted.
 
Ltac
soit_rayon_circonscrit A B C O r :=
elim (existence_rayon_circonscrit (A:=A) (B:=B) (C:=C)); [intros O | auto];
 intros toto; elim toto; clear toto; intro; intros toto; elim toto; clear toto;
 intros r; intro.
(* on doit pouvoir le demontrer*)
 
Axiom
   triangle_Sin_not_0 :
   forall A B C, triangle A B C ->  (Sin (cons_AV (vec A B) (vec A C)) <> 0).
#[export] Hint Resolve triangle_Sin_not_0 :geo.
 
Lemma triangle_abs_Sin_not_0:
 forall A B C,
 triangle A B C ->  (Rabs (Sin (cons_AV (vec A B) (vec A C))) <> 0).
Proof.
Admitted.
#[export] Hint Resolve triangle_abs_Sin_not_0 :geo.
(* Theoreme connu sous le nom de loi des Sinus.*)
 
Theorem loi_Sinus:
 forall A B C,
 triangle A B C ->
  and
   (distance B C / Rabs (Sin (cons_AV (vec A B) (vec A C))) =
    distance A B / Rabs (Sin (cons_AV (vec C A) (vec C B))))
   (distance B C / Rabs (Sin (cons_AV (vec A B) (vec A C))) =
    distance C A / Rabs (Sin (cons_AV (vec B C) (vec B A)))).
Proof.
Admitted.
 
Definition rayon_circonscrit (A B C : PO) (r : R) : Prop :=
   exists O : PO , circonscrit O A B C /\ r = distance O C .
 
Lemma triangle_sin_not_0:
 forall A B C x,
 triangle A B C -> image_angle x = cons_AV (vec A B) (vec A C) ->  (sin x <> 0).
Proof.
Admitted.
(* consequence de l'enroulement de la droite des reels sur le cercle trigonometrique dans le sens positif*)
 
Axiom sin_pos : forall (x : R), ( 0 <= x <= pi ) ->  (sin x >= 0).
 
Axiom
   non_multiple_pi_triangle :
   forall a A B C,
   ( 0 < a < pi ) ->
   A <> B ->
   A <> C -> image_angle a = cons_AV (vec A B) (vec A C) ->  triangle A B C.
(* debut de la demonstration du theoreme de Morley*)
 
Lemma pisurtrois_utile:
 forall a b c,
 0 < a -> 0 < b -> 0 < c -> (a + b) + c = pisurtrois ->  ( 0 <= 3 * a <= pi ).
Proof.
Admitted.
 
Lemma pisurtrois_utile1:
 forall a b c,
 0 < a -> 0 < b -> 0 < c -> (a + b) + c = pisurtrois ->  ( 0 <= b + c <= pi ).
Proof.
Admitted.
 
Lemma pisurtrois_utile2:
 forall a b c,
 0 < a -> 0 < b -> 0 < c -> (a + b) + c = pisurtrois ->  ( 0 <= c <= pi ).
Proof.
Admitted.
#[export] Hint Resolve pisurtrois_utile sin_pos pisurtrois_utile1 pisurtrois_utile2 :geo.
 
Lemma pisurtrois_triangle_utile:
 forall a b c A B C,
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C -> image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->  triangle A B C.
Proof.
Admitted.
 
Lemma pisurtrois_triangle_utile2:
 forall a b c B C P,
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 B <> C ->
 B <> P -> image_angle b = cons_AV (vec B C) (vec B P) ->  triangle B C P.
Proof.
Admitted.
 
Lemma Rabs_neg: forall (r : R), r <= 0 ->  Rabs r = - r.
Proof.
Admitted.
(* Application des theoremes rayon_Sinus et loi_Sinus dans un triangle forme par un cote et deux trissectrices.
   Calcul de la longueur du cote BP dans le triangle BPC.*)
 
Lemma Morley_1:
 forall (a b c r : R) (A B C P : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
  distance B P = (2 * (r * sin (3 * a))) * (sin c / sin (pisurtrois - a)).
Proof.
Admitted.
(* application de la formule sin 3 a  qui utilise pisurtrois dons le calcul de BP*)
 
Lemma Morley_2:
 forall (a b c r : R) (A B C P : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
  distance B P = (8 * (r * sin a)) * (sin c * sin (pisurtrois + a)).
Proof.
Admitted.
(* calcul de la longueur du cote  CP dans le triangle BPC*)
 
Lemma Morley_3:
 forall (a b c r : R) (A B C P : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
  distance C P = (8 * (r * sin a)) * (sin b * sin (pisurtrois + a)).
Proof.
Admitted.
(* on applique le lemme precedent dans un autre triangle ABQ forme par un cote et deux trissectrices*)
 
Lemma Morley_4:
 forall (a b c r : R) (A B C Q : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 A <> Q ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle (3 * c) = cons_AV (vec C A) (vec C B) ->
  distance B Q = (8 * (r * sin c)) * (sin a * sin (pisurtrois + c)).
Proof.
Admitted.
(*dans le triangle BPQ on peut caculer le 3eme cote en utilisant Al_Kashi*)
 
Lemma Morley_5:
 forall (a b c r : R) (A B C P Q : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 B <> Q ->
 A <> Q ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle b = cons_AV (vec B P) (vec B Q) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
 image_angle (3 * c) = cons_AV (vec C A) (vec C B) ->
  Rsqr (distance P Q) =
  (Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin c)))) *
  ((Rsqr (sin (pisurtrois + a)) + Rsqr (sin (pisurtrois + c))) -
   2 * (sin (pisurtrois + a) * (sin (pisurtrois + c) * cos b))).
Proof.
Admitted.
(* utilisation de la formule de trigonometrie Al_Kashi_pisurtrois pour simplifier le calcul.*)
 
Lemma Morley_6:
 forall (a b c r : R) (A B C P Q : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 B <> Q ->
 A <> Q ->
 rayon_circonscrit A B C r ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle b = cons_AV (vec B P) (vec B Q) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle (3 * a) = cons_AV (vec A B) (vec A C) ->
 image_angle (3 * c) = cons_AV (vec C A) (vec C B) ->
  Rsqr (distance P Q) =
  (Rsqr 8 * (Rsqr r * (Rsqr (sin a) * Rsqr (sin b)))) * Rsqr (sin c).
Proof.
Admitted.
 
Definition equilateral (A B C : PO) := and (isocele A B C) (isocele B C A).
(*Theoreme de Morley : utilisation de la symetrie de la formule pour conclure.*)
 
Theorem Morley:
 forall (a b c : R) (A B C P Q T : PO),
 0 < a ->
 0 < b ->
 0 < c ->
 (a + b) + c = pisurtrois ->
 A <> B ->
 A <> C ->
 B <> C ->
 B <> P ->
 B <> Q ->
 A <> T ->
 C <> T ->
 image_angle b = cons_AV (vec B C) (vec B P) ->
 image_angle b = cons_AV (vec B P) (vec B Q) ->
 image_angle b = cons_AV (vec B Q) (vec B A) ->
 image_angle c = cons_AV (vec C P) (vec C B) ->
 image_angle c = cons_AV (vec C T) (vec C P) ->
 image_angle a = cons_AV (vec A B) (vec A Q) ->
 image_angle a = cons_AV (vec A Q) (vec A T) ->
 image_angle a = cons_AV (vec A T) (vec A C) ->  equilateral P Q T.
Proof.
Admitted.
