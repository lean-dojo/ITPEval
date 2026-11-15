$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_92
  (verina__metamath__verina_basic_92), catalog title SwapArithmetic: the exact
  executable integer arithmetic program swaps two inputs as an ordered pair
  and satisfies its component and changed-position correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, ZZ X. ZZ is the product type of
  integer pairs, <. A , B >. is ordered-pair construction, and 1st and 2nd
  are its component projections.

  VERINAB92X1, VERINAB92Y1, VERINAB92X2, VERINAB92Y2, and VERINAB92X3
  preserve the source let-bound arithmetic sequence exactly: x1 is X, y1 is
  Y, x2 is y1 - x1, y2 is y1 - x2, and x3 is y2 + x2.
  VERINAB92SwapArithmetic returns exactly the source pair (x3,y2), so its
  executable result is fixed independently of the postcondition and admits no
  additional output.

  VERINAB92Pre is the source True precondition together with both Int input
  types. VERINAB92Post preserves both component equations and the conditional
  clause that unequal inputs leave each returned component unequal to the
  input formerly occupying that position. The proof-valued precondition
  arguments to the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this artifact adds no $p
  declaration.
$)

$c
  VERINAB92X1 VERINAB92Y1 VERINAB92X2 VERINAB92Y2 VERINAB92X3
  VERINAB92Pre VERINAB92SwapArithmetic VERINAB92Post
$.

verinab92-x1-syntax
  $a class ( VERINAB92X1 A ) $.
verinab92-y1-syntax
  $a class ( VERINAB92Y1 A ) $.
verinab92-x2-syntax
  $a class ( VERINAB92X2 A B ) $.
verinab92-y2-syntax
  $a class ( VERINAB92Y2 A B ) $.
verinab92-x3-syntax
  $a class ( VERINAB92X3 A B ) $.
verinab92-precondition-syntax
  $a wff ( VERINAB92Pre A B ) $.
verinab92-program-syntax
  $a class ( VERINAB92SwapArithmetic A B ) $.
verinab92-postcondition-syntax
  $a wff ( VERINAB92Post A B C ) $.

verinab92-x1-definition $a |- (
  VERINAB92X1 A
) = A $.

verinab92-y1-definition $a |- (
  VERINAB92Y1 A
) = A $.

verinab92-x2-definition $a |- (
  VERINAB92X2 A B
) = (
  ( VERINAB92Y1 B ) - ( VERINAB92X1 A )
) $.

verinab92-y2-definition $a |- (
  VERINAB92Y2 A B
) = (
  ( VERINAB92Y1 B ) - ( VERINAB92X2 A B )
) $.

verinab92-x3-definition $a |- (
  VERINAB92X3 A B
) = (
  ( VERINAB92Y2 A B ) + ( VERINAB92X2 A B )
) $.

verinab92-precondition-definition $a |- (
  VERINAB92Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab92-program-definition $a |- (
  VERINAB92SwapArithmetic A B
) = <.
  ( VERINAB92X3 A B ) ,
  ( VERINAB92Y2 A B )
>. $.

verinab92-postcondition-definition $a |- (
  VERINAB92Post A B C
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

verina-basic-92-swap-arithmetic $a |- A. x e. ZZ
  A. y e. ZZ
    (
      ( VERINAB92Pre x y )
      ->
      (
        VERINAB92Post
          x
          y
          ( VERINAB92SwapArithmetic x y )
      )
    )
$.
