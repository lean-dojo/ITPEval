$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_50
  (verina__metamath__verina_basic_50), catalog title Abs: the exact executable
  integer conditional returns the negation of a negative input and otherwise
  returns the input, with its absolute-value correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB50Pre is the source True
  precondition together with the Int input type.

  VERINAB50Abs is exactly the executable source program: it returns -x when
  x is strictly negative and x otherwise. Thus its result is fixed
  independently of the postcondition and admits no additional outputs.

  VERINAB50Post preserves the source conjunction without strengthening it:
  a nonnegative input must equal the result, and a negative input plus the
  result must equal zero. The proof-valued precondition arguments to the
  implementation and postcondition are computationally and propositionally
  unused and are represented by the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB50Pre VERINAB50Abs VERINAB50Post
$.

verinab50-precondition-syntax
  $a wff ( VERINAB50Pre A ) $.
verinab50-program-syntax
  $a class ( VERINAB50Abs A ) $.
verinab50-postcondition-syntax
  $a wff ( VERINAB50Post A B ) $.

verinab50-precondition-definition $a |- (
  VERINAB50Pre A
) <-> (
  A e. ZZ
) $.

verinab50-program-definition $a |- (
  VERINAB50Abs A
) = if (
  A < 0 ,
  ( -u A ) ,
  A
) $.

verinab50-postcondition-definition $a |- (
  VERINAB50Post A B
) <-> (
  (
    A e. ZZ
    /\
    B e. ZZ
  )
  /\
  (
    (
      0 <_ A
      ->
      A = B
    )
    /\
    (
      A < 0
      ->
      ( A + B ) = 0
    )
  )
) $.

verina-basic-50-abs $a |- A. x e. ZZ
  (
    ( VERINAB50Pre x )
    ->
    (
      VERINAB50Post
        x
        ( VERINAB50Abs x )
    )
  )
$.
