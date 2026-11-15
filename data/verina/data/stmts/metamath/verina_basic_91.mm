$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_91
  (verina__metamath__verina_basic_91), catalog title Swap: the exact
  executable integer program swaps two inputs as an ordered pair and
  satisfies its component and changed-position correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, ZZ X. ZZ is the product type of
  integer pairs, <. A , B >. is ordered-pair construction, and 1st and 2nd
  are its component projections.

  VERINAB91Pre is the source True precondition together with both Int input
  types. VERINAB91Swap preserves the source let-bound computation exactly:
  x is initialized to X, y to Y, tmp saves x, x is assigned y, y is assigned
  tmp, and the result is therefore the ordered pair <Y,X>.

  VERINAB91Post preserves both component equations and the conditional
  clause that unequal inputs leave each returned component unequal to the
  input formerly occupying that position. The proof-valued precondition
  arguments to the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this artifact adds no $p
  declaration.
$)

$c
  VERINAB91Pre VERINAB91Swap VERINAB91Post
$.

verinab91-precondition-syntax
  $a wff ( VERINAB91Pre A B ) $.
verinab91-program-syntax
  $a class ( VERINAB91Swap A B ) $.
verinab91-postcondition-syntax
  $a wff ( VERINAB91Post A B C ) $.

verinab91-precondition-definition $a |- (
  VERINAB91Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab91-program-definition $a |- (
  VERINAB91Swap A B
) = <. B , A >. $.

verinab91-postcondition-definition $a |- (
  VERINAB91Post A B C
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
    ( 1st ` C ) = B
    /\
    (
      ( 2nd ` C ) = A
      /\
      (
        A =/= B
        ->
        (
          ( 1st ` C ) =/= A
          /\
          ( 2nd ` C ) =/= B
        )
      )
    )
  )
) $.

verina-basic-91-swap $a |- A. x e. ZZ
  A. y e. ZZ
    (
      ( VERINAB91Pre x y )
      ->
      (
        VERINAB91Post
          x
          y
          ( VERINAB91Swap x y )
      )
    )
$.
