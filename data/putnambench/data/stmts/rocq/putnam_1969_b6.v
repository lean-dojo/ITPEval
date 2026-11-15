(* Statement-only formalization of PutnamBench artifact putnam_1969_b6:
   real matrices A and B whose product is the specified 3 by 3 matrix have
   reverse product equal to nine times the 2 by 2 identity. This file contains no proof. *)

From Stdlib Require Import Reals.

Open Scope R_scope.

Record Matrix32 : Type := {
  m32_00 : R;
  m32_01 : R;
  m32_10 : R;
  m32_11 : R;
  m32_20 : R;
  m32_21 : R
}.

Record Matrix23 : Type := {
  m23_00 : R;
  m23_01 : R;
  m23_02 : R;
  m23_10 : R;
  m23_11 : R;
  m23_12 : R
}.

Record Matrix33 : Type := {
  m33_00 : R;
  m33_01 : R;
  m33_02 : R;
  m33_10 : R;
  m33_11 : R;
  m33_12 : R;
  m33_20 : R;
  m33_21 : R;
  m33_22 : R
}.

Record Matrix22 : Type := {
  m22_00 : R;
  m22_01 : R;
  m22_10 : R;
  m22_11 : R
}.

Definition mul32_23 (A : Matrix32) (B : Matrix23) : Matrix33 :=
  {|
    m33_00 := m32_00 A * m23_00 B + m32_01 A * m23_10 B;
    m33_01 := m32_00 A * m23_01 B + m32_01 A * m23_11 B;
    m33_02 := m32_00 A * m23_02 B + m32_01 A * m23_12 B;
    m33_10 := m32_10 A * m23_00 B + m32_11 A * m23_10 B;
    m33_11 := m32_10 A * m23_01 B + m32_11 A * m23_11 B;
    m33_12 := m32_10 A * m23_02 B + m32_11 A * m23_12 B;
    m33_20 := m32_20 A * m23_00 B + m32_21 A * m23_10 B;
    m33_21 := m32_20 A * m23_01 B + m32_21 A * m23_11 B;
    m33_22 := m32_20 A * m23_02 B + m32_21 A * m23_12 B
  |}.

Definition mul23_32 (B : Matrix23) (A : Matrix32) : Matrix22 :=
  {|
    m22_00 :=
      m23_00 B * m32_00 A +
      m23_01 B * m32_10 A +
      m23_02 B * m32_20 A;
    m22_01 :=
      m23_00 B * m32_01 A +
      m23_01 B * m32_11 A +
      m23_02 B * m32_21 A;
    m22_10 :=
      m23_10 B * m32_00 A +
      m23_11 B * m32_10 A +
      m23_12 B * m32_20 A;
    m22_11 :=
      m23_10 B * m32_01 A +
      m23_11 B * m32_11 A +
      m23_12 B * m32_21 A
  |}.

Definition scalar_identity22 (c : R) : Matrix22 :=
  {|
    m22_00 := c;
    m22_01 := 0;
    m22_10 := 0;
    m22_11 := c
  |}.

Theorem putnam_1969_b6
    (A : Matrix32)
    (B : Matrix23)
    (p : Matrix33)
    (hp :
      m33_00 p = 8 /\
      m33_01 p = 2 /\
      m33_02 p = -2 /\
      m33_10 p = 2 /\
      m33_11 p = 5 /\
      m33_12 p = 4 /\
      m33_20 p = -2 /\
      m33_21 p = 4 /\
      m33_22 p = 5)
    (hAB : mul32_23 A B = p) :
  mul23_32 B A = scalar_identity22 9.
Admitted.
