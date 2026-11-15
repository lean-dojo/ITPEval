$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_44
  (verina__metamath__verina_basic_44), catalog title isOddAtIndexOdd: the
  exact executable indexed-array Boolean test returns true precisely when
  every odd valid index contains an odd integer, with its complete
  correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set. The Boolean domain is
  represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB44IsOdd is exactly the source Boolean helper n % 2 == 1. For the
  positive divisor two, SetMM integer remainder agrees with Lean's
  nonnegative Int remainder on every integer, including negative inputs.
  Natural indices are canonically integers, so applying this helper to an
  index preserves Lean's coercion from Nat to Int.

  VERINAB44MapIdxAll is the direct extensional expansion of the source local
  indexedArray followed by Array.all. Array.mapIdx creates exactly one pair
  (i, w[i]) for every valid index i, and the Boolean predicate
  !(isOdd i) || isOdd w[i] is true exactly when oddness of i implies oddness
  of w[i]. Thus the universal condition is equivalent in both directions to
  the complete mapIdx/all computation, including for the empty array.
  VERINAB44IsOddAtIndexOdd returns one exactly when this condition holds and
  zero otherwise, fixing the executable result independently of the
  postcondition and admitting no additional outputs.

  VERINAB44Pre is the source True precondition together with the Array Int
  input type. VERINAB44Post preserves the source equivalence between the
  Boolean result, interpreted as true exactly when it equals one, and the
  universal odd-index condition. The proof-valued precondition arguments to
  the implementation and postcondition have no computational or
  propositional effect beyond the explicit antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB44IsOdd VERINAB44MapIdxAll
  VERINAB44Pre VERINAB44IsOddAtIndexOdd VERINAB44Post
$.

verinab44-is-odd-syntax
  $a class ( VERINAB44IsOdd A ) $.
verinab44-map-idx-all-syntax
  $a wff ( VERINAB44MapIdxAll A ) $.
verinab44-precondition-syntax
  $a wff ( VERINAB44Pre A ) $.
verinab44-program-syntax
  $a class ( VERINAB44IsOddAtIndexOdd A ) $.
verinab44-postcondition-syntax
  $a wff ( VERINAB44Post A B ) $.

verinab44-is-odd-definition $a |- (
  VERINAB44IsOdd A
) = if (
  ( A mod 2 ) = 1 ,
  1 ,
  0
) $.

${
  $d i A $.

  verinab44-map-idx-all-definition $a |- (
    VERINAB44MapIdxAll A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      (
        ( VERINAB44IsOdd i ) = 1
        ->
        ( VERINAB44IsOdd ( A ` i ) ) = 1
      )
  ) $.
$}

verinab44-precondition-definition $a |- (
  VERINAB44Pre A
) <-> (
  A e. Word ZZ
) $.

verinab44-program-definition $a |- (
  VERINAB44IsOddAtIndexOdd A
) = if (
  ( VERINAB44MapIdxAll A ) ,
  1 ,
  0
) $.

${
  $d i A B $.

  verinab44-postcondition-definition $a |- (
    VERINAB44Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      B = 1
      <->
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          ( VERINAB44IsOdd i ) = 1
          ->
          ( VERINAB44IsOdd ( A ` i ) ) = 1
        )
    )
  ) $.
$}

verina-basic-44-is-odd-at-index-odd $a |- A. w e. Word ZZ
  (
    ( VERINAB44Pre w )
    ->
    (
      VERINAB44Post
        w
        ( VERINAB44IsOddAtIndexOdd w )
    )
  )
$.
