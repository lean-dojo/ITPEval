(***************************************************************************)
(* Formalization of the Chou, Gao and Zhang's decision procedure.          *)
(* Julien Narboux (Julien@narboux.fr)                                      *)
(* LIX/INRIA FUTURS 2004-2006                                              *)
(* University of Strasbourg 2008-2009                                      *)
(***************************************************************************)

Require Export euclidean_constructions.
Require Export area_elimination_lemmas.
Require Export ratios_elimination_lemmas.

(* lemme 3_2 chou *)
Lemma l_24_a : forall A B P D,
Col A D B -> perp A B P D ->
A<>B -> B<>D ->
 A**D / D**B = Py P A B / Py P B A.
Proof.
Admitted.

Lemma perp4_perp : forall A B P, 
perp A B P A -> Py P A B = 0.
Proof.
Admitted.

Lemma perp_not_eq_not_perp : forall A B P D, perp A B P D ->
Col A D B ->
 A <> B ->  B <> D -> A <> D -> 
Py P A B <> 0.
Proof.
Admitted.

(* lemma 3_2 chou *)
Lemma l_24_b : forall A B P D,
Col A D B -> perp A B P D ->
A<>B -> 
 A**D / A**B = Py P A B / (2 * A**B * A**B).
Proof.
Admitted.

(* lemma 3_2 chou *)
Lemma l_24_c : forall A B P D,
Col A D B -> perp A B P D ->
A<>B -> 
 D**B / A**B = Py P B A / (2 * A**B * A**B).
Proof.
Admitted.

Lemma l_24_c_on_foot : forall P U V Y,
on_foot Y P U V ->
U**Y / U**V = Py P U V / Py U V U.
Proof.
Admitted.

Lemma per_area: forall A B C,
  per A B C -> 
  2 * 2 * S A B C * S A B C = A**B * A**B * B**C * B**C.
Proof.
Admitted.

Lemma per_col_eq : forall A B C,
 per A B C -> Col A B C -> A = B \/ B = C.
Proof.
Admitted.

Lemma perp_col_perp : forall P Q B C,
 Q<>B ->
 per P Q B -> Col Q B C -> per P Q C.
Proof.
Admitted.

Lemma l_3_4 : forall A B C P,
 Col A B C -> Py P A C <> 0 ->
 Py P A B / Py P A C = A**B/ A**C.
Proof.
Admitted.

Require Export Classical.

Lemma per_dec : forall A B C,
 per A B C \/ ~ per A B C.
Proof.
Admitted.

Ltac cases_per A B C := elim (per_dec A B C);intros.

Lemma l_3_4_b : forall A B C P,
 Col A B C ->
 Py P A B * A**C =  Py P A C * A**B.
Proof.
Admitted.

Lemma l_28_b : forall A B U V Y,
U <> V ->
Col Y U V -> 
Py A B Y = U**Y/U**V * Py A B V + Y**V/U**V * Py A B U.
Proof.
Admitted.

Lemma l3_5_py : forall A B U V Y,
  U <> V ->
  Col Y U V ->  
  Py A Y B = U**Y / U**V * Py A V B + Y**V/ U**V * Py A U B 
  - (U**Y/ U**V) * (Y**V / U**V) * Py U V U.
Proof.
Admitted.

Lemma midpoint_ratio_1 : forall O B D,
mid_point O B D ->  B<>D -> B ** O / B ** D = 1/2.
Proof.
Admitted.

Lemma midpoint_ratio_2 : forall O B D,
mid_point O B D ->  B<>D -> O ** D / B ** D = 1/2.
Proof.
Admitted.

Lemma l_28_midpoint : forall O A B P Q,
 mid_point O A B ->
 2 * Py O P Q = Py A P Q + Py B P Q.
Proof.
Admitted.

Lemma l_28_b_midpoint : forall O A B P Q,
 mid_point O A B ->
 2 * Py P O Q = Py P A Q + Py P B Q - 1/ 2 * Py A B A.
Proof.
Admitted.

Lemma l_27_a : forall A B C D P Q, weak_3_parallelogram A B C D ->
Py A P Q + Py C P Q = Py B P Q + Py D P Q.
Proof.
Admitted.

Lemma l_27_b : forall A B C D P Q, weak_3_parallelogram A B C D ->
Py4 A P B Q = Py4 D P C Q.
Proof.
Admitted.

Lemma midpoint_is_midpoint: forall I A B, 
 mid_point I A B -> A<>B -> is_midpoint I A B.
Proof.
Admitted.

Lemma midpoint_on_line_d: forall I A B, 
 mid_point I A B -> A<>B -> on_line_d A I B (0-1).
Proof.
Admitted.

Lemma symmetric_point_unicity : forall O B C D, 
 mid_point O B D ->
 mid_point O D C ->
 B=C.
Proof.
Admitted.


Lemma weak_3_parallelogram_parallel : forall A B C D,
   weak_3_parallelogram A B C D -> parallel B C A D.
Proof.
Admitted.

Lemma eq_half_eq_zero : forall x : F, x = 1/2 * x -> x=0.
Proof.
Admitted.

Lemma weak_3_parallelogram_eq_side : forall A B C D,
   weak_3_parallelogram A B C D -> B**C= A**D.
Proof.
Admitted.


Lemma l3_6 : forall A B C D, 
  weak_3_parallelogram A B C D ->
 A**C * A**C + B**D * B**D = 2*A**B * A**B + 2*B**C*B**C.
Proof.
Admitted.

Lemma l3_6_b : forall A B C D, 
  weak_3_parallelogram A B C D ->
  Py A B C = - Py B A D.
Proof.
Admitted.


Lemma l_27_c : forall A B C D P Q, weak_3_parallelogram A B C D ->
Py P A Q + Py P C Q = Py P B Q + Py P D Q + 2 * Py B A D.
Proof.
Admitted.

Lemma l3_8_a : forall A B C D P, weak_3_parallelogram A B C D ->
Py P A B = Py4 P D A C.
Proof.
Admitted.

Lemma l3_8_b : forall A B C D P, weak_3_parallelogram A B C D ->
Py P A B = Py P D C - Py A D C.
Proof.
Admitted.

Lemma l_28_a : forall A B U V Y,
Col Y U V -> U <> V ->
S A B Y = U**Y/U**V * S A B V + Y**V/U**V * S A B U.
Proof.
Admitted.

Lemma on_foot_per : forall A B C F, 
  on_foot F A B C ->
  per A F B.
Proof.
Admitted.

Lemma herron_qin : forall A B C,
S A B C * S A B C = 1 / (2*2*2*2) * (Py A B A * Py A C A - Py B A C * Py B A C).
Proof.
Admitted.

Lemma l3_9_aux : forall B D P Q R S Y ,
 Col Y B D ->
 B<>D ->
 B ** Y = Q ** S ->
 weak_3_parallelogram B Y S Q ->
 Py4 P Q R S = Q ** S / B ** D * Py4 P B R D.
Proof.
Admitted.

Lemma l3_9 : forall P Q R S A B C D,
  parallel P R A C ->
  parallel Q S B D ->
  B<>D -> A<>C -> ~ perp A C B D ->
  Py4 P Q R S / Py4 A B C D = (P**R / A**C) * (Q**S / B**D).
Proof.
Admitted.


Lemma l3_10 : forall A B C D,
 parallel A B C D ->
 C<>D ->
 A**B/C**D = Py4 A C B D / - Py C D C.
Proof.
Admitted.

Lemma l3_10b : forall A B C D,
 parallel A B C D ->
 C<>D ->
 A**B/C**D = Py4 B C A D / Py C D C.
Proof.
Admitted.

Lemma perp_not_parallel : forall A B C D,
  perp A B C D ->
  A <> B -> C <> D ->
  ~ parallel A B C D.
Proof.
Admitted.

Lemma not_perp_to_itself : forall A B,
A <> B ->~ perp A B A B.
Proof.
Admitted.

Lemma parallel_not_perp : forall A B C D,
  parallel A B C D ->
  A <> B -> C <> D ->
  ~ perp A B C D.
Proof.
Admitted.



Lemma l_25_a : forall A B P Q Y,
  P<>Q -> Q<>Y -> Py Q A B <> 0 ->
 on_inter_line_perp Y A P Q A B ->
 P**Y / Q**Y = Py P A B / Py Q A B.
Proof.
Admitted.

Lemma l_25_b : forall A B P Q Y,
  P<>Q -> Q<>Y -> Py Q A B <> 0 ->
 on_inter_line_perp Y A P Q A B ->
 P**Y / P**Q = Py P A B / Py4 P A Q B.
Proof.
Admitted.

Lemma l_25_c : forall A B P Q Y,
  P<>Q -> Q<>Y -> Py Q A B <> 0 ->
 on_inter_line_perp Y A P Q A B ->
 Q**Y / P**Q = Py Q A B / Py4 P A Q B.
Proof.
Admitted.

