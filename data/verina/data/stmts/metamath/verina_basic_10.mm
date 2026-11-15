$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_10
  (verina__metamath__verina_basic_10), catalog title isGreater: the exact
  executable finite-integer-array test returns true precisely when the given
  integer is strictly greater than every array entry, with its nonempty-array
  precondition and Boolean correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays. For a word w, # ` w is its natural-number
  length, w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  index set. The Boolean domain is represented by { 0 , 1 }, with false = 0
  and true = 1.

  VERINAB10AllGreater is the elementwise strict comparison computed by the
  source Array.all call. VERINAB10IsGreater returns one exactly when that
  comparison holds and zero otherwise, so the implementation is fixed
  independently of the postcondition and admits no additional outputs.

  VERINAB10Pre preserves the source positive-size precondition.
  VERINAB10Post preserves the source equivalence between the universal
  indexed comparison and the Boolean result. The proof-valued precondition
  argument is computationally and propositionally unused and is represented
  by the explicit precondition antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB10AllGreater VERINAB10Pre VERINAB10IsGreater VERINAB10Post
$.

verinab10-all-greater-syntax
  $a wff ( VERINAB10AllGreater A B ) $.
verinab10-precondition-syntax
  $a wff ( VERINAB10Pre A B ) $.
verinab10-program-syntax
  $a class ( VERINAB10IsGreater A B ) $.
verinab10-postcondition-syntax
  $a wff ( VERINAB10Post A B C ) $.

${
  $d i A B $.

  verinab10-all-greater-definition $a |- (
    VERINAB10AllGreater A B
  ) <-> (
    (
      A e. ZZ
      /\
      B e. Word ZZ
    )
    /\
    A. i e. ( 0 ..^ ( # ` B ) )
      ( B ` i ) < A
  ) $.
$}

verinab10-precondition-definition $a |- (
  VERINAB10Pre A B
) <-> (
  (
    A e. ZZ
    /\
    B e. Word ZZ
  )
  /\
  0 < ( # ` B )
) $.

verinab10-program-definition $a |- (
  VERINAB10IsGreater A B
) = if (
  ( VERINAB10AllGreater A B ) ,
  1 ,
  0
) $.

${
  $d i A B C $.

  verinab10-postcondition-definition $a |- (
    VERINAB10Post A B C
  ) <-> (
    (
      (
        A e. ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. { 0 , 1 }
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` B ) )
        ( B ` i ) < A
      <->
      C = 1
    )
  ) $.
$}

verina-basic-10-is-greater $a |- A. n e. ZZ
  A. w e. Word ZZ
    (
      ( VERINAB10Pre n w )
      ->
      (
        VERINAB10Post
          n
          w
          ( VERINAB10IsGreater n w )
      )
    )
$.
