$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_41 (verina__metamath__verina_advanced_41), catalog title
  maxOfThree: the exact nested-conditional integer program returns one of
  three arbitrary integers and a value at least as large as each input.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINA41Pre is the source True
  precondition together with the three input types. VERINA41MaxOfThree is
  exactly the executable source program: it returns A when A is at least B
  and C, otherwise returns B when B is at least A and C, and returns C in
  the remaining case.

  VERINA41Post requires the result to be an integer at least as large as
  every input and equal to one of the three inputs. The proof-valued
  precondition argument is computationally and propositionally unused and
  is omitted from the target function and postcondition predicate. The final
  $a declaration is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this artifact adds no $p declaration.
$)

$c VERINA41Pre VERINA41MaxOfThree VERINA41Post $.

verina41-precondition-syntax
  $a wff ( VERINA41Pre A B C ) $.
verina41-max-of-three-syntax
  $a class ( VERINA41MaxOfThree A B C ) $.
verina41-postcondition-syntax
  $a wff ( VERINA41Post A B C D ) $.

verina41-precondition-definition $a |- (
  VERINA41Pre A B C
) <-> (
  (
    A e. ZZ
    /\
    B e. ZZ
  )
  /\
  C e. ZZ
) $.

verina41-max-of-three-definition $a |- (
  VERINA41MaxOfThree A B C
) = if (
  (
    B <_ A
    /\
    C <_ A
  ) ,
  A ,
  if (
    (
      A <_ B
      /\
      C <_ B
    ) ,
    B ,
    C
  )
) $.

verina41-postcondition-definition $a |- (
  VERINA41Post A B C D
) <-> (
  (
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
    D e. ZZ
  )
  /\
  (
    (
      (
        A <_ D
        /\
        B <_ D
      )
      /\
      C <_ D
    )
    /\
    (
      D = A
      \/
      (
        D = B
        \/
        D = C
      )
    )
  )
) $.

verina-advanced-41-max-of-three $a |- A. a e. ZZ
  A. b e. ZZ
    A. c e. ZZ
      (
        ( VERINA41Pre a b c )
        ->
        (
          VERINA41Post
            a
            b
            c
            ( VERINA41MaxOfThree a b c )
        )
      )
$.
