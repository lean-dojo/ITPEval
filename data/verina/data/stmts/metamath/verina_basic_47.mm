$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_47
  (verina__metamath__verina_basic_47), catalog title arraySum: the exact
  executable summation of all entries of a nonempty finite integer array
  returns its total and satisfies the recursive-prefix-sum correctness
  contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and their
  toList conversions. For a word w, # ` w is its natural-number length,
  w ` k is zero-based lookup, and 0 ..^ n is exactly { 0, ..., n - 1 }.

  VERINAB47GetBang reproduces Lean Array.get! on integer arrays for natural
  indices, including its inhabited default value zero outside the array.
  VERINAB47ToList is Array.toList, extensionally the identity on this finite
  word representation. VERINAB47ListSum is the exact List.sum fold over all
  entries. Therefore VERINAB47ArraySum preserves the source implementation
  a.toList.sum and fixes its executable result independently of the
  postcondition.

  VERINAB47SumTo is the finite sum of get!-values at indices below n. It is
  definitionally equivalent to the source recursion: the value at zero is
  zero, and the value at n + 1 is the value at n plus get! at n. This remains
  exact when n exceeds the array size because get! then contributes zero.

  VERINAB47Pre is exactly the positive-size precondition. VERINAB47Post
  preserves both source conjuncts: result minus sumTo at the array size is
  zero, and result is at least that same sum. The proof-valued precondition
  arguments to the implementation and postcondition have no computational or
  propositional effect beyond the explicit antecedent in the final
  correctness assertion. The source proof-only auxiliary theorem is not part
  of the statement package. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB47GetBang VERINAB47ToList VERINAB47ListSum
  VERINAB47Pre VERINAB47ArraySum VERINAB47SumTo VERINAB47Post
$.

verinab47-get-bang-syntax
  $a class ( VERINAB47GetBang A B ) $.
verinab47-to-list-syntax
  $a class ( VERINAB47ToList A ) $.
verinab47-list-sum-syntax
  $a class ( VERINAB47ListSum A ) $.
verinab47-precondition-syntax
  $a wff ( VERINAB47Pre A ) $.
verinab47-program-syntax
  $a class ( VERINAB47ArraySum A ) $.
verinab47-sum-to-syntax
  $a class ( VERINAB47SumTo A B ) $.
verinab47-postcondition-syntax
  $a wff ( VERINAB47Post A B ) $.

verinab47-get-bang-definition $a |- (
  VERINAB47GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab47-to-list-definition $a |- (
  VERINAB47ToList A
) = A $.

${
  $d k A $.

  verinab47-list-sum-definition $a |- (
    VERINAB47ListSum A
  ) = (
    sum_ k e. ( 0 ..^ ( # ` A ) )
      ( A ` k )
  ) $.
$}

verinab47-precondition-definition $a |- (
  VERINAB47Pre A
) <-> (
  (
    A e. Word ZZ
    /\
    0 < ( # ` A )
  )
) $.

verinab47-program-definition $a |- (
  VERINAB47ArraySum A
) = (
  VERINAB47ListSum
    ( VERINAB47ToList A )
) $.

${
  $d k A B $.

  verinab47-sum-to-definition $a |- (
    VERINAB47SumTo A B
  ) = (
    sum_ k e. ( 0 ..^ B )
      ( VERINAB47GetBang A k )
  ) $.
$}

verinab47-postcondition-definition $a |- (
  VERINAB47Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    (
      B - (
        VERINAB47SumTo A ( # ` A )
      )
    ) = 0
    /\
    (
      VERINAB47SumTo A ( # ` A )
    ) <_ B
  )
) $.

verina-basic-47-array-sum $a |- A. w e. Word ZZ
  (
    ( VERINAB47Pre w )
    ->
    (
      VERINAB47Post
        w
        ( VERINAB47ArraySum w )
    )
  )
$.
