(* This file takes 9 seconds to process on a 2023 gaming computer *)
From Stdlib Require Import List BinNat ZArith Zdivisibility Zmod QArith Rbase RNsatz.

(* Example with a generic domain *)

Section test.

Lemma nonconsecutive_equalities_to_goal (FR ep : Z) (IHp : FR = ep) a : (fst a * snd a + FR = fst a * snd a + ep)%Z.
Proof.
Admitted.

Lemma example3_Z : forall (x y z : Z), (
  x+y+z=0 ->
  x*y+x*z+y*z=0->
  x*y*z=0 -> x*x*x=0)%Z.
Proof.
Admitted.

Lemma example3_Zmod3 : forall (x y z : Zmod 3), (
  x+y+z=0 ->
  x*y+x*z+y*z=0->
  x*y*z=0 -> x^3=0)%Zmod.
Proof.
Admitted.

Lemma example3_Zmodp : forall p (x y z : Zmod p), Z.
Proof.
Admitted.

Lemma example3_Q : forall (x y z : Q), (
  x+y+z==0 ->
  x*y+x*z+y*z==0->
  x*y*z==0 -> x*x*x==0)%Q.
Proof.
Admitted.

Lemma example3_R : forall (x y z : R), (
  x+y+z=0 ->
  x*y+x*z+y*z=0->
  x*y*z=0 -> x*x*x=0)%R.
Proof.
Admitted.

Lemma example_contradiction_Zmod3 : forall (x : Zmod 3), (
  x = Zmod.
Proof.
Admitted.

Lemma example_contradiction_Zmodp : forall p (x : Zmod p), Z.
Proof.
Admitted.

Import Integral_domain Algebra_syntax.

Context {A:Type}`{Aid:Integral_domain A}.

Lemma example3_A : forall (x y z :A),
  x+y+z==0 ->
  x*y+x*z+y*z==0->
  x*y*z==0 -> x^3%Z==0.
Proof.
Admitted.

Lemma example4 : forall x y z u,
  x+y+z+u==0 ->
  x*y+x*z+x*u+y*z+y*u+z*u==0->
  x*y*z+x*y*u+x*z*u+y*z*u==0->
  x*y*z*u==0 -> x^4%Z==0.
Proof.
Admitted.

Lemma example5 : forall x y z u v,
  x+y+z+u+v==0 ->
  x*y+x*z+x*u+x*v+y*z+y*u+y*v+z*u+z*v+u*v==0->
  x*y*z+x*y*u+x*y*v+x*z*u+x*z*v+x*u*v+y*z*u+y*z*v+y*u*v+z*u*v==0->
  x*y*z*u+y*z*u*v+z*u*v*x+u*v*x*y+v*x*y*z==0 ->
  x*y*z*u*v==0 -> x^5%Z==0.
Proof.
Admitted.

Goal forall x y:Z,  x = y -> (x+0)%Z = (y*1+0)%Z.
Proof.
Admitted.

Goal forall x y:R,  x = y -> (x+0)%R = (y*1+0)%R.
Proof.
Admitted.

Goal forall a b c x:R, a = b -> b = c -> (a*a)%R = (c*c)%R.
Proof.
Admitted.

End test.

Section Geometry.
Import Algebra_syntax List.ListNotations.
#[local] Open Scope R_scope.
#[local] Coercion IZR : Z >-> R.

(* See the interactive pictures of Laurent Théry
   on http://www-sop.inria.fr/marelle/CertiGeo/
   and research paper on
   https://docs.google.com/fileview?id=0ByhB3nPmbnjTYzFiZmIyNGMtYTkwNC00NWFiLWJiNzEtODM4NmVkYTc2NTVk&hl=fr
*)

Record point:Type:={
 X:R;
 Y:R}.

Definition collinear(A B C:point):=
  (X A - X B)*(Y C - Y B)-(Y A - Y B)*(X C - X B)=0.

Definition parallel (A B C D:point):=
  ((X A)-(X B))*((Y C)-(Y D))=((Y A)-(Y B))*((X C)-(X D)).

Definition notparallel (A B C D:point)(x:R):=
  x*(((X A)-(X B))*((Y C)-(Y D))-((Y A)-(Y B))*((X C)-(X D)))=1.

Definition orthogonal (A B C D:point):=
  ((X A)-(X B))*((X C)-(X D))+((Y A)-(Y B))*((Y C)-(Y D))=0.

Definition equal2(A B:point):=
  (X A)=(X B) /\ (Y A)=(Y B).

Definition equal3(A B:point):=
  ((X A)-(X B))^2%Z+((Y A)-(Y B))^2%Z = 0.

Definition nequal2(A B:point):=
  (X A)<>(X B) \/ (Y A)<>(Y B).

Definition nequal3(A B:point):=
  not (((X A)-(X B))^2%Z+((Y A)-(Y B))^2%Z = 0).

Definition middle(A B I:point):=
  2%R*(X I)=(X A)+(X B) /\ 2%R*(Y I)=(Y A)+(Y B).

Definition distance2(A B:point):=
  (X B - X A)^2%Z + (Y B - Y A)^2%Z.

(* AB = CD *)
Definition samedistance2(A B C D:point):=
  (X B - X A)^2%Z + (Y B - Y A)^2%Z = (X D - X C)^2%Z + (Y D - Y C)^2%Z.
Definition determinant(A O B:point):=
  (X A - X O)*(Y B - Y O) - (Y A - Y O)*(X B - X O).
Definition scalarproduct(A O B:point):=
  (X A - X O)*(X B - X O) + (Y A - Y O)*(Y B - Y O).
Definition norm2(A O B:point):=
  ((X A - X O)^2%Z+(Y A - Y O)^2%Z)*((X B - X O)^2%Z+(Y B - Y O)^2%Z).

Definition equaldistance(A B C D:point):=
  ((X B) - (X A))^2%Z + ((Y B) - (Y A))^2%Z =
  ((X D) - (X C))^2%Z + ((Y D) - (Y C))^2%Z.

Definition equaltangente(A B C D E F:point):=
  let s1:= determinant A B C in
  let c1:= scalarproduct A B C in
  let s2:= determinant D E F in
  let c2:= scalarproduct D E F in
  s1 * c2 = s2 * c1.

Ltac cnf2 f :=
  match f with
   | ?A \/ (?B /\ ?C) =>
     let c1 := cnf2 (A\/B) in
     let c2 := cnf2 (A\/C) in constr:(c1/\c2)
   | (?B /\ ?C) \/ ?A =>
     let c1 := cnf2 (B\/A) in
     let c2 := cnf2 (C\/A) in constr:(c1/\c2)
   | (?A \/ ?B) \/ ?C =>
     let c1 := cnf2 (B\/C) in cnf2 (A \/ c1)
   | _ => f
  end
with cnf f :=
  match f with
   | ?A \/ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         cnf2 (c1 \/ c2)
   | ?A /\ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         constr:(c1 /\ c2)
   | _ => f
  end.

Ltac scnf :=
  match goal with
    | |- ?f => let c := cnf f in
      assert c;[repeat split| tauto]
  end.

Ltac disj_to_pol f :=
  match f with
   | ?a = ?b \/ ?g => let p := disj_to_pol g in constr:((a - b)* p)
   | ?a = ?b => constr:(a - b)
  end.

Lemma fastnsatz1:forall x y:R, x - y = 0 -> x = y.
Proof.
Admitted.

Ltac fastnsatz:=
  try trivial; try apply fastnsatz1; try trivial; nsatz.

Ltac proof_pol_disj :=
  match goal with
   | |- ?g => let p := disj_to_pol g in
     let h := fresh "hp" in
     assert (h:p = 0);
     [idtac|
      prod_disj h p]
   | _ => idtac
  end
with prod_disj h p :=
  match goal with
   | |- ?a = ?b \/ ?g =>
        match p with
          | ?q * ?p1 =>
        let h0 := fresh "hp" in
        let h1 := fresh "hp" in
        let h2 := fresh "hp" in
        assert (h0:a - b = 0 \/ p1 = 0);
        [apply Rmult_integral; exact h|
         destruct h0 as [h1|h2];
         [left; fastnsatz|
          right; prod_disj h2 p1]]
        end
   | _ => fastnsatz
  end.

(*
Goal forall a b c d e f:R, a=b \/ c=d \/ e=f \/ e=a.
Proof.
Admitted.

Lemma Pythagore: forall A B C:point,
  orthogonal A B A C ->
  distance2 A C + distance2 A B = distance2 B C.
Proof.
Admitted.

Lemma Thales: forall O A B C D:point,
  collinear O A C -> collinear O B D ->
  parallel A B C D ->
  (distance2 O B * distance2 O C = distance2 O D * distance2 O A
  /\ distance2 O B * distance2 C D = distance2 O D * distance2 A B)
 \/ collinear O A B.
Proof.
Admitted.

Lemma segments_of_chords: forall A B C D M O:point,
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  collinear A B M ->
  collinear C D M ->
  (distance2 M A) * (distance2 M B) = (distance2 M C) * (distance2 M D)
  \/ parallel A B C D.
Proof.
Admitted.

Lemma isoceles: forall A B C:point,
  equaltangente A B C B C A ->
  distance2 A B = distance2 A C
  \/ collinear A B C.
Proof.
Admitted.

Lemma minh: forall A B C D O E H I:point,
  X A = 0 -> Y A = 0 -> Y O = 0 ->
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  orthogonal A C B D ->
  collinear A C E ->
  collinear B D E ->
  collinear A B H ->
  orthogonal E H A B ->
  collinear C D I ->
  middle C D I ->
  collinear H E I
  \/ (X C)^2%Z * (X B)^5%Z * (X O)^2%Z
     * (X C - 2%Z * X O)^3%Z * (-2%Z * X O + X B)=0
  \/  parallel A C B D.
Proof.
Admitted.

Lemma Pappus: forall A B C A1 B1 C1 P Q S:point,
  X A = 0 -> Y A = 0 -> Y B = 0 -> Y C = 0 ->
  collinear A1 B1 C1 ->
  collinear A B1 P -> collinear A1 B P ->
  collinear A C1 Q -> collinear A1 C Q ->
  collinear B C1 S -> collinear B1 C S ->
  collinear P Q S
  \/ (Y A1 - Y B1)^2%Z=0 \/ (X A = X B1)
  \/ (X A1 = X C) \/ (X C = X B1)
  \/ parallel A B1 A1 B \/ parallel A C1 A1 C \/ parallel B C1 B1 C.
Proof.
Admitted.

Lemma Simson: forall A B C O D E F G:point,
  X A = 0 -> Y A = 0 ->
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  orthogonal  E D B C ->
  collinear B C E ->
  orthogonal F D A C ->
  collinear A C F ->
  orthogonal G D A B ->
  collinear A B G ->
  collinear E F G
  \/ (X C)^2%Z = 0 \/ (Y C)^2%Z = 0 \/ (X B)^2%Z = 0 \/ (Y B)^2%Z = 0 \/ (Y C - Y B)^2%Z = 0
  \/ equal3 B A
  \/ equal3 A C \/ (X C - X B)^2%Z = 0
  \/ equal3 B C.
Proof.
Admitted.

Lemma threepoints: forall A B C A1 B1 A2 B2 H1 H2 H3:point,
  (* H1 intersection of bisections *)
  middle B C A1 ->  orthogonal H1 A1 B C ->
  middle A C B1 -> orthogonal H1 B1 A C ->
  (* H2 intersection of medians *)
  collinear A A1 H2 -> collinear B B1 H2 ->
  (* H3 intersection of altitudes *)
  collinear B C A2 ->  orthogonal A A2 B C ->
  collinear A C B2 -> orthogonal B B2 A C ->
  collinear A A1 H3 -> collinear B B1 H3 ->
  collinear H1 H2 H3
  \/ collinear A B C.
Proof.
Admitted.

Lemma Feuerbach:  forall A B C A1 B1 C1 O A2 B2 C2 O2:point,
  forall r r2:R,
  X A = 0 -> Y A =  0 -> X B = 1 -> Y B =  0->
  middle A B C1 -> middle B C A1 -> middle C A B1 ->
  distance2 O A1 = distance2 O B1 ->
  distance2 O A1 = distance2 O C1 ->
  collinear A B C2 -> orthogonal A B O2 C2 ->
  collinear B C A2 -> orthogonal B C O2 A2 ->
  collinear A C B2 -> orthogonal A C O2 B2 ->
  distance2 O2 A2 = distance2 O2 B2 ->
  distance2 O2 A2 = distance2 O2 C2 ->
  r^2%Z = distance2 O A1 ->
  r2^2%Z = distance2 O2 A2 ->
  distance2 O O2 = (r + r2)^2%Z
  \/ distance2 O O2 = (r - r2)^2%Z
  \/ collinear A B C.
Proof.
Admitted.

Lemma Euler_circle: forall A B C A1 B1 C1 A2 B2 C2 O:point,
  middle A B C1 -> middle B C A1 -> middle C A B1 ->
  orthogonal A B C C2 -> collinear A B C2 ->
  orthogonal B C A A2 -> collinear B C A2 ->
  orthogonal A C B B2 -> collinear A C B2 ->
  distance2 O A1 = distance2 O B1 ->
  distance2 O A1 = distance2 O C1 ->
  (distance2 O A2 = distance2 O A1
   /\distance2 O B2 = distance2 O A1
   /\distance2 O C2 = distance2 O A1)
  \/ collinear A B C.
Proof.
Admitted.

Lemma Desargues: forall A B C A1 B1 C1 P Q T S:point,
  X S = 0 -> Y S = 0 -> Y A = 0 ->
  collinear A S A1 -> collinear B S B1 -> collinear C S C1 ->
  collinear B1 C1 P -> collinear B C P ->
  collinear A1 C1 Q -> collinear A C Q ->
  collinear A1 B1 T -> collinear A B T ->
  collinear P Q T
  \/ X A = X B \/ X A = X C \/ X B = X C  \/ X A = 0 \/ Y B = 0 \/ Y C = 0
  \/ collinear S B C \/ parallel A C A1 C1 \/ parallel A B A1 B1.
Proof.
Admitted.

Lemma chords: forall O A B C D M:point,
  equaldistance O A O B ->
  equaldistance O A O C ->
  equaldistance O A O D ->
  collinear A B M -> collinear C D M ->
  scalarproduct A M B = scalarproduct C M D
  \/ parallel A B C D.
Proof.
Admitted.

Lemma Ceva: forall A B C D E F M:point,
  collinear M A D -> collinear M B E -> collinear M C F ->
  collinear B C D -> collinear E A C -> collinear F A B ->
  (distance2 D B) * (distance2 E C) * (distance2 F A) =
  (distance2 D C) * (distance2 E A) * (distance2 F B)
  \/ collinear A B C.
Proof.
Admitted.

Lemma bissectrices: forall A B C M:point,
  equaltangente C A M M A B ->
  equaltangente A B M M B C ->
  equaltangente B C M M C A
  \/ equal3 A B.
Proof.
Admitted.

Lemma bisections: forall A B C A1 B1 C1 H:point,
  middle B C A1 ->  orthogonal H A1 B C ->
  middle A C B1 -> orthogonal H B1 A C ->
  middle A B C1 ->
  orthogonal H C1 A B
  \/ collinear A B C.
Proof.
Admitted.

Lemma altitudes: forall A B C A1 B1 C1 H:point,
  collinear B C A1 ->  orthogonal A A1 B C ->
  collinear A C B1 -> orthogonal B B1 A C ->
  collinear A B C1 -> orthogonal C C1 A B ->
  collinear A A1 H -> collinear B B1 H ->
  collinear C C1 H
  \/ equal2 A B
  \/ collinear A B C.
Proof.
Admitted.

Lemma hauteurs:forall A B C A1 B1 C1 H:point,
  collinear B C A1 ->  orthogonal A A1 B C ->
  collinear A C B1 -> orthogonal B B1 A C ->
  collinear A B C1 -> orthogonal C C1 A B ->
  collinear A A1 H -> collinear B B1 H ->

  collinear C C1 H
  \/ collinear A B C.
Proof.
Admitted.


End Geometry.
