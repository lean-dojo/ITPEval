$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_4
  (verina__metamath__verina_basic_4), catalog title kthElement: the exact
  bounds-defaulted integer-array lookup at the one-based natural position
  returns that array entry under the valid-position precondition and satisfies
  the source Array.any correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set.

  VERINAB4NatSub is Lean's truncated natural subtraction.
  VERINAB4GetBang reproduces Lean Array.get! on integer arrays, including its
  inhabited default value zero outside the array. VERINAB4KthElement applies
  that exact lookup at k - 1, so the executable output is fixed independently
  of the postcondition and admits no additional results.

  VERINAB4Pre preserves 1 <= k <= arr.size. VERINAB4Post preserves the source
  Array.any predicate by requiring a valid array index whose entry equals both
  the result and the same bounds-defaulted lookup at k - 1. The proof-valued
  precondition argument has no computational effect and is not inspected by
  the postcondition, so it is represented by the explicit antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB4NatSub VERINAB4GetBang
  VERINAB4Pre VERINAB4KthElement VERINAB4Post
$.

verinab4-nat-sub-syntax
  $a class ( VERINAB4NatSub A B ) $.
verinab4-get-bang-syntax
  $a class ( VERINAB4GetBang A B ) $.
verinab4-precondition-syntax
  $a wff ( VERINAB4Pre A B ) $.
verinab4-program-syntax
  $a class ( VERINAB4KthElement A B ) $.
verinab4-postcondition-syntax
  $a wff ( VERINAB4Post A B C ) $.

verinab4-nat-sub-definition $a |- (
  VERINAB4NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab4-get-bang-definition $a |- (
  VERINAB4GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab4-precondition-definition $a |- (
  VERINAB4Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. NN0
  )
  /\
  (
    1 <_ B
    /\
    B <_ ( # ` A )
  )
) $.

verinab4-program-definition $a |- (
  VERINAB4KthElement A B
) = (
  VERINAB4GetBang
    A
    ( VERINAB4NatSub B 1 )
) $.

${
  $d i A B C $.

  verinab4-postcondition-definition $a |- (
    VERINAB4Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. ZZ
    )
    /\
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        ( A ` i ) = C
        /\
        ( A ` i ) = (
          VERINAB4GetBang
            A
            ( VERINAB4NatSub B 1 )
        )
      )
  ) $.
$}

verina-basic-4-kth-element $a |- A. w e. Word ZZ
  A. k e. NN0
    (
      ( VERINAB4Pre w k )
      ->
      (
        VERINAB4Post
          w
          k
          ( VERINAB4KthElement w k )
      )
    )
$.
