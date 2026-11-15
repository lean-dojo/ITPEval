$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_96
  (verina__metamath__verina_basic_96), catalog title SwapSimultaneous: the
  exact executable integer-pair program simultaneously swaps its two inputs
  and satisfies its component and changed-position correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, ZZ X. ZZ is the product type of
  integer pairs, <. A , B >. is ordered-pair construction, and 1st and 2nd
  are its component projections.

  VERINAB96Pre is the source True precondition together with both Int input
  types. VERINAB96SwapSimultaneous is exactly the source executable pair
  (Y,X), so its result is fixed independently of the postcondition and admits
  no additional output. VERINAB96Post preserves both component equations and
  the conditional clause that unequal inputs leave each returned component
  unequal to the input formerly occupying that position.

  The proof-valued precondition arguments to the implementation and
  postcondition are computationally and propositionally unused beyond the
  explicit precondition antecedent in the final correctness assertion. Every
  earlier $a is syntax or a faithful definition required by this rendering,
  and this database has no $p declaration.
$)

$c
  VERINAB96Pre VERINAB96SwapSimultaneous VERINAB96Post
$.

verinab96-precondition-syntax
  $a wff ( VERINAB96Pre A B ) $.
verinab96-program-syntax
  $a class ( VERINAB96SwapSimultaneous A B ) $.
verinab96-postcondition-syntax
  $a wff ( VERINAB96Post A B C ) $.

verinab96-precondition-definition $a |- (
  VERINAB96Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab96-program-definition $a |- (
  VERINAB96SwapSimultaneous A B
) = <. B , A >. $.

verinab96-postcondition-definition $a |- (
  VERINAB96Post A B C
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

verina-basic-96-swap-simultaneous $a |- A. x e. ZZ
  A. y e. ZZ
    (
      ( VERINAB96Pre x y )
      ->
      (
        VERINAB96Post
          x
          y
          ( VERINAB96SwapSimultaneous x y )
      )
    )
$.
