$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_78
  (verina__metamath__verina_basic_78), catalog title MultipleReturns: the
  exact executable integer program returns the sum and difference of two
  integers as an ordered pair and satisfies its component correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, ZZ X. ZZ is the product type of
  integer pairs, <. A , B >. is ordered-pair construction, and 1st and 2nd
  are its component projections.

  VERINAB78Pre is the source True precondition together with both Int input
  types. VERINAB78MultipleReturns preserves the source let-bound computation
  exactly: it computes more = x + y and less = x - y, then returns
  (more, less). VERINAB78Post preserves the source equations that the first
  result component is x + y and the second result component plus y is x.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this artifact adds no $p declaration.
$)

$c
  VERINAB78Pre VERINAB78MultipleReturns VERINAB78Post
$.

verinab78-precondition-syntax
  $a wff ( VERINAB78Pre A B ) $.
verinab78-program-syntax
  $a class ( VERINAB78MultipleReturns A B ) $.
verinab78-postcondition-syntax
  $a wff ( VERINAB78Post A B C ) $.

verinab78-precondition-definition $a |- (
  VERINAB78Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab78-program-definition $a |- (
  VERINAB78MultipleReturns A B
) = <.
  ( A + B ) ,
  ( A - B )
>. $.

verinab78-postcondition-definition $a |- (
  VERINAB78Post A B C
) <-> (
  (
    (
      A e. ZZ
      /\
      B e. ZZ
    )
    /\
    C e. ( ZZ X. ZZ )
  )
  /\
  (
    ( 1st ` C ) = ( A + B )
    /\
    ( ( 2nd ` C ) + B ) = A
  )
) $.

verina-basic-78-multiple-returns $a |- A. x e. ZZ
  A. y e. ZZ
    (
      ( VERINAB78Pre x y )
      ->
      (
        VERINAB78Post
          x
          y
          ( VERINAB78MultipleReturns x y )
      )
    )
$.
