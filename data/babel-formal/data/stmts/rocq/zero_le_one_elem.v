Class DecidableEqAlt (A : Type) := {
  dec_eq : forall x y : A, {x = y} + {x <> y}
}.

Class ZeroAlt (A : Type) := zero : A.
Class OneAlt  (A : Type) := one  : A.

Class Preorder (A : Type) := {
  le                  : A -> A -> Prop;
  Preorder_Reflexive  : forall x,       le x x;
  Preorder_Transitive : forall x y z,   le x y -> le y z -> le x z
}.

Infix "≤" := le (at level 70, no associativity).

Class ZeroLEOneClass (A : Type)
      `{ZeroAlt A} `{OneAlt A} `{Preorder A} := {
  zero_le_one : zero ≤ (one : A);
  zero_le_zero : zero ≤ (zero : A)
}.

Section Matrix.
  Variable (m : Type).
  Context `{DecidableEqAlt m}.

  Variable (α : Type).
  Context `{ZeroLEOneClass α}.

  Definition matrix := m -> m -> α.

  Definition One_matrix : matrix :=
    fun i j => if dec_eq i j then one else zero.

  Lemma zero_le_one_elem (i j : m) :
    zero ≤ (One_matrix : matrix) i j.
Proof.
Admitted.

  Definition Zero_matrix : matrix := fun _ _ => zero.

  Definition matrix_le (A B : matrix) : Prop :=
    forall i j, A i j ≤ B i j.
  Infix "≤ₘ" := matrix_le (at level 70).

  Lemma Zero_le_One_matrix : Zero_matrix ≤ₘ One_matrix.
Proof.
Admitted.

  Lemma matrix_le_refl (A : matrix) : A ≤ₘ A.
Proof.
Admitted.

  Lemma matrix_le_trans (A B C : matrix) :
    A ≤ₘ B -> B ≤ₘ C -> A ≤ₘ C.
Proof.
Admitted.

  Definition matrix_eq (A B : matrix) : Prop :=
    forall i j, A i j = B i j.
  Infix "≃ₘ" := matrix_eq (at level 70).

  Lemma matrix_eq_refl (A : matrix) : A ≃ₘ A.
Proof.
Admitted.

  Lemma matrix_eq_sym (A B : matrix) : A ≃ₘ B -> B ≃ₘ A.
Proof.
Admitted.

  Lemma matrix_eq_trans (A B C : matrix) :
    A ≃ₘ B -> B ≃ₘ C -> A ≃ₘ C.
Proof.
Admitted.

  Lemma matrix_eq_le (A B : matrix) :
    A ≃ₘ B -> A ≤ₘ B /\ B ≤ₘ A.
Proof.
Admitted.

  Class PartialOrder (A : Type) `{Preorder A} := {
    le_antisym : forall x y, x ≤ y -> y ≤ x -> x = y
  }.
  Context {PO : PartialOrder α}.

  Lemma matrix_le_antisymm (A B : matrix) :
    A ≤ₘ B -> B ≤ₘ A -> A ≃ₘ B.
Proof.
Admitted.
End Matrix.
