$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_11
  (verina__metamath__verina_basic_11), catalog title lastDigit: the exact
  executable natural-number remainder-by-ten program returns the final
  decimal digit and satisfies its range and equality correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain. VERINAB11NatSub is Lean's
  truncated natural subtraction. VERINAB11Pre is the source True
  precondition together with the Nat input type.

  VERINAB11LastDigit is exactly the executable source expression n % 10.
  VERINAB11Post preserves the source conjunction that the result lies from
  zero through nine and that both truncated differences between n % 10 and
  the result are zero. Thus the implementation is fixed independently of
  the postcondition and permits no additional outputs.

  The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit precondition
  antecedent in the final correctness assertion. Every earlier $a is syntax
  or a faithful definition required by this rendering, and this database has
  no $p declaration.
$)

$c
  VERINAB11NatSub VERINAB11Pre VERINAB11LastDigit VERINAB11Post
$.

verinab11-nat-sub-syntax
  $a class ( VERINAB11NatSub A B ) $.
verinab11-precondition-syntax
  $a wff ( VERINAB11Pre A ) $.
verinab11-program-syntax
  $a class ( VERINAB11LastDigit A ) $.
verinab11-postcondition-syntax
  $a wff ( VERINAB11Post A B ) $.

verinab11-nat-sub-definition $a |- (
  VERINAB11NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab11-precondition-definition $a |- (
  VERINAB11Pre A
) <-> (
  A e. NN0
) $.

verinab11-program-definition $a |- (
  VERINAB11LastDigit A
) = (
  A mod ; 1 0
) $.

verinab11-postcondition-definition $a |- (
  VERINAB11Post A B
) <-> (
  (
    A e. NN0
    /\
    B e. NN0
  )
  /\
  (
    (
      0 <_ B
      /\
      B < ; 1 0
    )
    /\
    (
      (
        VERINAB11NatSub
          ( A mod ; 1 0 )
          B
      ) = 0
      /\
      (
        VERINAB11NatSub
          B
          ( A mod ; 1 0 )
      ) = 0
    )
  )
) $.

verina-basic-11-last-digit $a |- A. n e. NN0
  (
    ( VERINAB11Pre n )
    ->
    (
      VERINAB11Post
        n
        ( VERINAB11LastDigit n )
    )
  )
$.
