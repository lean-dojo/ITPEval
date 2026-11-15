$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_88
  (verina__metamath__verina_basic_88), catalog title ToArray: the exact
  executable conversion of an arbitrary finite integer list to an array
  preserves its length and every element in the same order. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists and arrays. For a word w, # ` w is its
  natural-number length or size, w ` i is zero-based lookup, and NN0 is the
  full natural-number domain.

  VERINAB88Pre is the source True precondition on typed List Int inputs.
  VERINAB88ToArray is exactly List.toArray: because the finite-word
  representation is shared by lists and arrays, the conversion is
  extensionally the identity and fixes the output independently of the
  postcondition. VERINAB88Post preserves the source size equality and its
  universally quantified valid-index get!-equality. Under the bound on i
  and the size equality, both word lookups are exactly the corresponding
  Lean List.get! and Array.get! values.

  The proof-valued precondition arguments have no computational or
  propositional effect beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c VERINAB88Pre VERINAB88ToArray VERINAB88Post $.

verinab88-precondition-syntax
  $a wff ( VERINAB88Pre A ) $.
verinab88-program-syntax
  $a class ( VERINAB88ToArray A ) $.
verinab88-postcondition-syntax
  $a wff ( VERINAB88Post A B ) $.

verinab88-precondition-definition $a |- (
  VERINAB88Pre A
) <-> (
  A e. Word ZZ
) $.

verinab88-program-definition $a |- (
  VERINAB88ToArray A
) = A $.

${
  $d i A B $.

  verinab88-postcondition-definition $a |- (
    VERINAB88Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. NN0
        (
          i < ( # ` A )
          ->
          ( B ` i ) = ( A ` i )
        )
    )
  ) $.
$}

verina-basic-88-to-array $a |- A. w e. Word ZZ
  (
    ( VERINAB88Pre w )
    ->
    (
      VERINAB88Post
        w
        ( VERINAB88ToArray w )
    )
  )
$.
