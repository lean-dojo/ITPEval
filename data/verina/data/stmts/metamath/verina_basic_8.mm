$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_8
  (verina__metamath__verina_basic_8), catalog title myMin: the exact
  executable non-strict comparison returns the smaller of two integers and
  satisfies its lower-bound and input-selection correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB8Pre is the source True
  precondition together with the two Int input types.

  VERINAB8MyMin is exactly the executable source expression: it returns A
  when A <= B and returns B otherwise. In particular, it returns A when the
  inputs are equal. Thus the implementation and its tie behavior are fixed
  independently of the postcondition and admit no additional outputs.

  VERINAB8Post preserves the source conjunction: the result is no greater
  than either input and equals one of the two inputs. The proof-valued
  precondition argument is computationally and propositionally unused and is
  represented by the explicit precondition antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c VERINAB8Pre VERINAB8MyMin VERINAB8Post $.

verinab8-precondition-syntax
  $a wff ( VERINAB8Pre A B ) $.
verinab8-program-syntax
  $a class ( VERINAB8MyMin A B ) $.
verinab8-postcondition-syntax
  $a wff ( VERINAB8Post A B C ) $.

verinab8-precondition-definition $a |- (
  VERINAB8Pre A B
) <-> (
  A e. ZZ
  /\
  B e. ZZ
) $.

verinab8-program-definition $a |- (
  VERINAB8MyMin A B
) = if (
  A <_ B ,
  A ,
  B
) $.

verinab8-postcondition-definition $a |- (
  VERINAB8Post A B C
) <-> (
  (
    (
      A e. ZZ
      /\
      B e. ZZ
    )
    /\
    C e. ZZ
  )
  /\
  (
    (
      C <_ A
      /\
      C <_ B
    )
    /\
    (
      C = A
      \/
      C = B
    )
  )
) $.

verina-basic-8-my-min $a |- A. a e. ZZ
  A. b e. ZZ
    (
      ( VERINAB8Pre a b )
      ->
      (
        VERINAB8Post
          a
          b
          ( VERINAB8MyMin a b )
      )
    )
$.
