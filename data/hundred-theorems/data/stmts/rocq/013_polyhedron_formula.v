(*==========================================================
============================================================
            TOPOLOGICAL FMAPS, QHMAPS, HMAPS -

       PROOFS OF THE GENUS THEOREM AND THE EULER RELATION 

                        PART 3:

  EQUIVALENCES, CHARACTERISTICS, GENUS, EULER_POINCARE, 
         CONSTRUCTIVE CONDITION OF PLANARITY 

       (J.-F. Dufourd - June 2006 - FOR PUBLICATION
        completed in October 2007 / January 2008)

(* COMPLETE, APART FROM LEMMA expf_clos_symm, WHICH IS 
ADMITTED TO PROVE THE NECESSARY CONDITION OF PLANARITY *)
============================================================
==========================================================*)

(*==========================================================
           DART EQUIVALENCES IN QHMAPS
==========================================================*)

Require Export Euler2.

(* Face equivalence: *)

Definition eqf(m:fmap)(x y:dart):=
  expf m x y \/ expf m y x.

(* Reflexivity of eqf: *)

Lemma refl_eqf : forall (m:fmap)(x:dart),
  exd m x -> eqf m x x.
Proof.
Admitted.

(* Symmetry of eqf: *)

Lemma symm_eqf : forall (m:fmap)(x y:dart),
  eqf m x y -> eqf m y x.
Proof.
Admitted.

(* Transitivity of eqf: *)

Lemma trans_eqf : forall (m:fmap),
  inv_qhmap m -> forall (x y z:dart),
  eqf m x y -> eqf m y z -> eqf m x z.
Proof.
Admitted.

(* Decidability of eqf: *)

Lemma eqf_dec : forall (m:fmap)(x y:dart),
  {eqf m x y} + {~eqf m x y}.
Proof.
Admitted.

(* Connectivity : Definition in Prop "a la" Warshall *)

Fixpoint eqc(m:fmap)(x y:dart){struct m}:Prop:=
 match m with
     V => False
  |  I m0 x0 => x=x0 /\ y=x0 \/ eqc m0 x y
  |  L m0 _ x0 y0 =>
      eqc m0 x y
     \/ eqc m0 x x0 /\ eqc m0 y0 y
     \/ eqc m0 x y0 /\ eqc m0 x0 y
 end.

(* Decidability of eqc: *)

Lemma eqc_dec : forall (m:fmap)(x y:dart),
   {eqc m x y} + {~eqc m x y}.
Proof.
Admitted.

(* Reflexivity of eqc: *)

Lemma refl_eqc: forall(m:fmap)(x:dart),
   exd m x -> eqc m x x.
Proof.
Admitted.

(* Symmetry of eqc: *)

Lemma symm_eqc: forall(m:fmap)(x y:dart),
   eqc m x y -> eqc m y x.
Proof.
Admitted.

(* Transitivity of eqc: *)

Lemma trans_eqc: forall(m:fmap)(x y z:dart),
   eqc m x y -> eqc m y z -> eqc m x z.
Proof.
Admitted.

(* LEMMAS, USED IN THE FOLLOWING: *)

Lemma succ_eqc_A_r : forall m:fmap,
 inv_qhmap m ->
  forall (k:dim)(x:dart),
      succ m k x -> eqc m x (A m k x).
Proof.
Admitted.

(* Idem, for A_1: *)

Lemma pred_eqc_A_1_r : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x:dart),
     pred m k x -> eqc m x (A_1 m k x).
Proof.
Admitted.

(* OK: *)

Lemma eqc_eqc_A_1_l : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   eqc m x y -> pred m k x -> eqc m (A_1 m k x) y.
Proof.
Admitted.

(* INVERSES, Idem: *)

Lemma eqc_A_1_l_eqc : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   pred m k x ->  eqc m (A_1 m k x) y -> eqc m x y.
Proof.
Admitted.

(* OK: *)

Lemma eqc_A_r_eqc : forall m:fmap, inv_qhmap m ->
 forall (k:dim)(x y:dart),
   succ m k y ->  eqc m x (A m k y) -> eqc m x y.
Proof.
Admitted.

(* Face path implies equivalence: with the LEMMAS above: *)

Lemma expf_eqc : forall m:fmap,
 inv_qhmap m ->
   forall (x y:dart), expf m x y -> eqc m x y.
Proof.
Admitted.

(* OK: *)

Lemma expf_A_1_l_eqc : forall m:fmap,
 inv_qhmap m ->
   forall (x y:dart)(k:dim),
       expf m (A_1 m k x) y -> eqc m x y.
Proof.
Admitted.

(* IDEM : *)

Lemma expf_A_r_eqc : forall(m:fmap)(k:dim),
 inv_qhmap m ->
   forall (x y:dart), expf m x (A m k y) -> eqc m x y.
Proof.
Admitted.

(*========================================================
      	      NUMBERING AND CHARACTERISTICS:
=========================================================*)

Require Import ZArith.
Open Scope Z_scope.

(* Number of darts: *)

Fixpoint nd(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nd m0 + 1
  | L m0 _ _ _ => nd m0
 end.

(* Number of vertices: *)

Fixpoint nv(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nv m0 + 1
  | L m0 di0 x y => nv m0
  | L m0 di1 x y => nv m0 -
      if eq_dart_dec (A (clos m0) di1 x) y
      then 0 else 1
 end.

(* Number of edges: *)

Fixpoint ne(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => ne m0 + 1
  | L m0 di0 x y => ne m0 -
      if eq_dart_dec (A (clos m0) di0 x) y
      then 0 else 1
  | L m0 di1 x y => ne m0
 end.

(* Number of faces: *)

Fixpoint nf(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nf m0 + 1
  | L m0 di0 x y =>
      let mc := clos m0 in
      let x0 := A mc di0 x in
      let x_1:= A_1 mc di1 x in
      nf m0 +
       if eq_dart_dec y x0 then 0
       else if expf_dec mc x_1 y then 1
	    else -1
  | L m0 di1 x y =>
      let mc := clos m0 in
      let x1 := A mc di1 x in
      let y0 := A mc di0 y in
      nf m0 +
       if eq_dart_dec y x1 then 0
       else if expf_dec mc x y0 then 1
	    else -1
 end.

(* Number of connected components: *)

Fixpoint nc(m:fmap):Z :=
 match m with
    V => 0
  | I m0 x => nc m0 + 1
  | L m0 _ x y => nc m0 -
       if eqc_dec (clos m0) x y then 0 else 1
 end.

(* Euler-Poincare characteristic: *)

Definition ec(m:fmap): Z:=
  nv m + ne m + nf m - nd m.

(* The Euler-Poincare characteristic is even: OK: *)

Theorem even_ec : forall m:fmap, Zeven (ec m).
Proof.
Admitted.

(* THEOREME OF THE GENUS: OK *)

Theorem genus_theorem : forall m:fmap,
  inv_qhmap m -> 2 * (nc m) >= (ec m).
Proof.
Admitted.

Definition genus(m:fmap):= (nc m) - (ec m)/2.

(* COROLLARY, OK: *)

Theorem genus_corollary : forall m:fmap,
  inv_qhmap m -> genus m >= 0.
Proof.
Admitted.

Definition planar(m:fmap):= genus m = 0.

(* EULER-POINCARE FORMULA: *)

Lemma Euler_Poincare: forall m:fmap,
  inv_qhmap m -> planar m ->
    ec m / 2 = nc m.
Proof.
Admitted.

(* REMARK: SYMMETRY OF expf in the closure NOT USED *)

(* ==========================================================
         PLANARITY CRITERIA (SUFFICIENT CONDITIONS)  
=============================================================*)

(* Sewing at dimension 0: *)

Lemma expf_planar_0: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di0 x y -> let mc:= clos m in
    expf mc (A_1 mc di1 x) y -> 
      planar (L m di0 x y).
Proof.
Admitted.

(* Sewing at dimension 1: *) 

Lemma expf_planar_1: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m ->
    prec_Lq m di1 x y -> let mc:= clos m in
      expf mc x (A mc di0 y) -> 
        planar (L m di1 x y).
Proof.
Admitted.

(* V is planar: *)

Lemma planar_V: planar V.
Proof.
Admitted.

(* Inserting a dart preserves planarity: *)

Lemma planar_I: forall (m:fmap)(x:dart),
  inv_qhmap m -> planar m -> prec_I m x -> 
       planar (I m x).
Proof.
Admitted.

(* Sewing two disconnected darts preserves planarity:*)
 
Lemma not_eqc_planar: forall (m:fmap)(k:dim)(x y:dart),
  inv_qhmap m -> planar m ->  prec_Lq m k x y -> 
     let mc:= clos m in ~eqc mc x y -> 
         planar (L m k x y).
Proof.
Admitted.

(* Sewing at dimension 0 and planarity preservation: *)

Lemma expf_planar_L0: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di0 x y -> let mc:= clos m in
     (~eqc mc x y \/ expf mc (A_1 mc di1 x) y) -> 
        planar (L m di0 x y).
Proof.
Admitted.

(* Sewing at dimension 1 and planarity preservation: *)

Lemma expf_planar_L1: forall (m:fmap)(x y:dart),
  inv_qhmap m -> planar m -> 
   prec_Lq m di1 x y -> let mc:= clos m in
    (~eqc mc x y \/ expf mc x (A mc di0 y)) -> 
       planar (L m di1 x y).
Proof.
Admitted.

(* Definition of "Planar formation" of fmap: *)

Fixpoint plf(m:fmap):Prop:=
  match m with 
     V => True
   | I m0 x => plf m0
   | L m0 di0 x y => plf m0 /\ 
      (let mc := (clos m0) in
        ~eqc mc x y \/ expf mc (A_1 mc di1 x) y)
   | L m0 di1 x y => plf m0 /\ 
      (let mc := (clos m0) in
        ~eqc mc x y \/ expf mc x (A mc di0 y))
  end.

(* Constructive Sufficient Condition of planarity: *)

Theorem plf_planar:forall (m:fmap),
  inv_qhmap m -> plf m -> planar m.
Proof.
Admitted.

(* plf_EULER-POINCARE FORMULA: *)

Theorem plf_Euler_Poincare: forall m:fmap,
  inv_qhmap m -> plf m ->
     ec m / 2 = nc m.
Proof.
Admitted.

(* ==========================================================
       
        PLANARITY CRITERIA (NECESSARY CONDITIONS)  

OK, modulo expf SYMMETRY!!
=============================================================*)

(* OK: *)

Lemma eq_genus_I : forall(m:fmap)(x:dart),
   inv_qhmap (I m x) -> genus (I m x) = genus m.
Proof.
Admitted.

Lemma incr_genus_L0:forall(m:fmap)(x y:dart),
  inv_qhmap (L m di0 x y) ->
     genus m <= genus (L m di0 x y).
Proof.
Admitted.

Lemma incr_genus_L1:forall(m:fmap)(x y:dart),
  inv_qhmap (L m di1 x y) ->
     genus m <= genus (L m di1 x y).
Proof.
Admitted.

Lemma planar_I_rcp: forall(m:fmap)(x:dart),
  inv_qhmap (I m x) -> planar (I m x) -> planar m.
Proof.
Admitted.

Lemma planar_L0_rcp: forall(m:fmap)(x y:dart),
  inv_qhmap (L m di0 x y) -> 
     planar (L m di0 x y) -> planar m.
Proof.
Admitted.

Lemma planar_L1_rcp: forall(m:fmap)(x y:dart),
  inv_qhmap (L m di1 x y) -> 
    planar (L m di1 x y) -> planar m.
Proof.
Admitted.

Lemma succf_expf_F: forall(m:fmap)(x:dart),
  inv_qhmap m -> succf m x -> expf m x (F m x).
Proof.
Admitted.

(* HYPOTHESIS: VERY IMPORTANT!!! *)

Lemma expf_clos_symm: forall(m:fmap)(x y:dart),
  inv_qhmap m -> expf (clos m) x y -> expf (clos m) y x.
Proof.
Admitted.

Lemma expf_planar_L1_rcp: forall (m:fmap)(x y:dart),
   inv_qhmap (L m di1 x y) -> planar (L m di1 x y) -> 
      let mc:= clos m in
        (~eqc mc x y \/ expf mc x (A mc di0 y)).
Proof.
Admitted.

Theorem plf_planar_rcp: forall m:fmap,
  inv_qhmap m -> genus m = 0 -> plf m.
Proof.
Admitted.

(* Corollary: *)

Theorem plf_Euler_Poincare_rcp: forall m:fmap,
  inv_qhmap m -> ec m / 2 = nc m -> plf m.
Proof.
Admitted.

(* Corollary: CHARACTERIZATION OF THE PLANAR POLYHEDRA: *)

Theorem Euler_Poincare_criterion: forall m:fmap,
  inv_qhmap m -> (plf m <-> ec m / 2 = nc m).
Proof.
Admitted.

(*==========================================================
============================================================

		      THE END

============================================================
===========================================================*)

