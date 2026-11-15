$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_59
  (verina__metamath__verina_basic_59), catalog title DoubleQuadruple: the
  exact executable integer program returns a pair whose first component is
  twice the input and whose second component is twice the first. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, ZZ X. ZZ is the product type of
  integer pairs, <. A , B >. is ordered-pair construction, and 1st and 2nd
  are its component projections.

  VERINAB59Pre is the source True precondition together with the Int input
  type. VERINAB59DoubleQuadruple preserves the source let-bound computation
  exactly: it first computes a = 2 * x and then b = 2 * a before returning
  the pair (a, b). VERINAB59Post preserves the source equations that the
  first result component equals 2 * x and the second equals twice the first
  result component.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this artifact adds no $p declaration.
$)

$c
  VERINAB59Pre VERINAB59DoubleQuadruple VERINAB59Post
$.

verinab59-precondition-syntax
  $a wff ( VERINAB59Pre A ) $.
verinab59-program-syntax
  $a class ( VERINAB59DoubleQuadruple A ) $.
verinab59-postcondition-syntax
  $a wff ( VERINAB59Post A B ) $.

verinab59-precondition-definition $a |- (
  VERINAB59Pre A
) <-> (
  A e. ZZ
) $.

verinab59-program-definition $a |- (
  VERINAB59DoubleQuadruple A
) = <.
  ( 2 x. A ) ,
  ( 2 x. ( 2 x. A ) )
>. $.

verinab59-postcondition-definition $a |- (
  VERINAB59Post A B
) <-> (
  (
    A e. ZZ
    /\
    B e. ( ZZ X. ZZ )
  )
  /\
  (
    ( 1st ` B ) = ( 2 x. A )
    /\
    ( 2nd ` B ) = ( 2 x. ( 1st ` B ) )
  )
) $.

verina-basic-59-double-quadruple $a |- A. x e. ZZ
  (
    ( VERINAB59Pre x )
    ->
    (
      VERINAB59Post
        x
        ( VERINAB59DoubleQuadruple x )
    )
  )
$.
