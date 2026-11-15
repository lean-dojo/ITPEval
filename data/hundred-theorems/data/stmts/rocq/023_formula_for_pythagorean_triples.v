(* Pythagorean.v *)

(***********************)
(* Pythagorean triples *)
(***********************)

Require Export Tactics.

(* A non nul predicate *)
Definition nnl_triple (a b c : Z) := ~(a = 0) /\ ~(b = 0) /\ ~(c = 0).

(* A positive predicate *)
Definition pos_triple (a b c : Z) := (a >= 0) /\ (b >= 0) /\ (c >= 0).

(* A Pythagorean predicate *)
Definition is_pytha (a b c : Z) := (pos_triple a b c) /\ a * a + b * b = c * c.

(* Unit circle and D_r *)
Definition in_ucirc (x y : R) := (x * x + y * y = 1)%R.
Definition D_r (r x y : R) := (y = r * (x + 1))%R.

(******************************)
(* Set of Pythagorean triples *)
(******************************)

(* step1 *)

Lemma pytha_ucirc1 : forall a b c : Z,
  (c > 0) -> (is_pytha a b c) -> (in_ucirc (frac a c) (frac b c)).
Proof.
Admitted.

Lemma pytha_ucirc2 : forall a b c : Z, (a >= 0) /\ (b >= 0) /\ (c > 0) ->
  (in_ucirc (frac a c) (frac b c)) -> (is_pytha a b c).
Proof.
Admitted.

(* step 2 *)

(* Intersection between the unit circle and D_r *)
Definition interCDr (r x y : R) := (in_ucirc x y) /\ (D_r r x y).

(* Points of the intersection *)
Definition p1 := (-1,0)%R.
Definition p2 (r : R) :=
  let den := (1 + r * r)%R in
  ((1 - r * r) / den, 2 * r / den)%R.

(* Equality over points *)
Definition eqp (p1 p2 : R * R) := (fst p1) = (fst p2) /\ (snd p1)= (snd p2).

(* Total order over points (using R) *)
Lemma ordp : forall p1 p2 : R * R, (eqp p1 p2) \/ ~(eqp p1 p2).
Proof.
Admitted.

(* Characterization of the intersection *)
Lemma interCDr_sol : forall r x y : R,
  (interCDr r x y) -> (eqp (x,y) p1) \/ (eqp (x,y) (p2 r)).
Proof.
Admitted.

(* step 3 *)

Lemma rat_coo1 : forall x y : R, (in_ucirc x y) /\
  (exists r : R, (is_rat r) /\ (interCDr r x y)) -> (is_ratp (x,y)).
Proof.
Admitted.

Lemma rat_coo2 : forall x y : R, (in_ucirc x y) /\ (is_ratp (x,y)) ->
  exists r : R, (is_rat r) /\ (interCDr r x y).
Proof.
Admitted.

(* step 4 *)

(* Positivity predicate over points *)
Definition is_posp (c : R * R) := (fst c >= 0)%R /\ (snd c >= 0)%R.

(* Predicate for the positive rational coordinates of the unit circle *)
Definition is_ucp (c : R * R) :=
  (in_ucirc (fst c) (snd c)) /\ (is_ratp c) /\ (is_posp c).

(* Positive rational coordinates of the unit circle *)
Definition ucp (p q : Z) :=
  let pr := (IZR p) in
  let qr := (IZR q) in
  let den := (pr * pr + qr * qr)%R in
  ((qr * qr - pr * pr) / den, (2 * pr * qr) / den)%R.

(* A basic condition over p and q *)
Definition cond_pqb (p q : Z) := p >= 0 /\ q > 0 /\ p <= q /\ (rel_prime p q).

(* Set of positive rational coordinates of the unit circle *)
Definition in_ucp_setb (x y : R) :=
  exists p : Z, exists q : Z,
  x = (fst (ucp p q)) /\ y = (snd (ucp p q)) /\ (cond_pqb p q).

Lemma rat_pos_coo1 : forall x y : R, (is_ucp (x,y)) ->
  exists r : R, (is_rat r) /\ (r >= 0)%R /\ (r <= 1)%R /\ x = (fst (p2 r)) /\
  y = (snd (p2 r)).
Proof.
Admitted.

Lemma rat_pos_coo2 : forall x y : R, (is_ucp (x,y)) -> (in_ucp_setb x y).
Proof.
Admitted.

(* Step 5 *)

(* The full condition over p and q *)
Definition cond_pq (p q : Z) := cond_pqb p q /\ (distinct_parity p q).

(* The (new) set of positive rational coordinates of the unit circle *)
Definition in_ucp_set (x y : R) :=
  exists p : Z, exists q : Z,
  (x = (fst (ucp p q)) /\ y = (snd (ucp p q)) \/
   x = (snd (ucp p q)) /\ y = (fst (ucp p q))) /\ (cond_pq p q).

(* Inclusion of in_ucp_set in in_ucp_setb *)
Lemma nrat_pos_coo1 : forall x y : R, (in_ucp_set x y) -> (in_ucp_setb x y).
Proof.
Admitted.

(* Inclusion of in_ucp_setb in in_ucp_set *)
Lemma nrat_pos_coo2 : forall x y : R, (in_ucp_setb x y) -> (in_ucp_set x y).
Proof.
Admitted.

(* step 6 *)

(* The set of Pythagorean triples *)
Definition pytha_set (a b c : Z) :=
  exists p : Z, exists q : Z, exists m : Z,
    (a = m * (q * q - p * p) /\ b = 2 * m * (p * q) \/
     a = 2 * m * (p * q) /\ b = m * (q * q - p * p)) /\
    c = m * (p * p + q * q) /\ m >= 0 /\ (cond_pq p q).

(* Relative primality and fractions *)
Lemma relp_frac : forall a b c d : Z,
  (b <> 0) -> (d <> 0) -> (frac a b) = (frac c d) -> (rel_prime c d) ->
  exists m : Z, m <> 0 /\ b = m * d.
Proof.
Admitted.

Lemma pytha_thm1 : forall a b c : Z, (is_pytha a b c) -> (pytha_set a b c).
Proof.
Admitted.

Lemma pytha_thm2 : forall a b c : Z, (pytha_set a b c) -> (is_pytha a b c).
Proof.
Admitted.

(* A specific case *)

Definition pytha_set_even (a b c : Z) :=
  exists p : Z, exists q : Z, exists m : Z,
    a = m * (q * q - p * p) /\ b = 2 * m * (p * q) /\
    c = m * (p * p + q * q) /\ m >= 0 /\ (cond_pq p q).

Lemma pytha_thm3 : forall a b c : Z,
  is_pytha a b c -> Zodd a -> pytha_set_even a b c.
Proof.
Admitted.
