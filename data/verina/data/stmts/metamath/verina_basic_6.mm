$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_6
  (verina__metamath__verina_basic_6), catalog title minOfThree: the exact
  executable nested comparison returns the minimum of three integers and
  satisfies its lower-bound and input-membership correctness contract. This
  file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain. VERINAB6Pre is the source True
  precondition together with the three Int input types.

  VERINAB6MinOfThree is exactly the executable source program. It returns A
  when A <= B and A <= C; otherwise it returns B when B <= A and B <= C;
  otherwise it returns C. Thus the implementation, including its deterministic
  branch order on ties, is fixed independently of the postcondition and admits
  no additional outputs.

  VERINAB6Post preserves the source conjunction: the result is no greater than
  each input and equals one of the three inputs. The proof-valued precondition
  argument is computationally and propositionally unused and is represented by
  the explicit precondition antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB6Pre VERINAB6MinOfThree VERINAB6Post
$.

verinab6-precondition-syntax
  $a wff ( VERINAB6Pre A B C ) $.
verinab6-program-syntax
  $a class ( VERINAB6MinOfThree A B C ) $.
verinab6-postcondition-syntax
  $a wff ( VERINAB6Post A B C D ) $.

verinab6-precondition-definition $a |- (
  VERINAB6Pre A B C
) <-> (
  (
    A e. ZZ
    /\
    B e. ZZ
  )
  /\
  C e. ZZ
) $.

verinab6-program-definition $a |- (
  VERINAB6MinOfThree A B C
) = if (
  (
    A <_ B
    /\
    A <_ C
  ) ,
  A ,
  if (
    (
      B <_ A
      /\
      B <_ C
    ) ,
    B ,
    C
  )
) $.

verinab6-postcondition-definition $a |- (
  VERINAB6Post A B C D
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
      D <_ A
      /\
      (
        D <_ B
        /\
        D <_ C
      )
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

verina-basic-6-min-of-three $a |- A. a e. ZZ
  A. b e. ZZ
    A. c e. ZZ
      (
        ( VERINAB6Pre a b c )
        ->
        (
          VERINAB6Post
            a
            b
            c
            ( VERINAB6MinOfThree a b c )
        )
      )
$.
