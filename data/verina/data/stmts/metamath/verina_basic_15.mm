$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_15
  (verina__metamath__verina_basic_15), catalog title
  containsConsecutiveNumbers: the exact executable indexed integer-array scan
  returns true precisely when some entry plus one equals its following entry,
  with its unrestricted-input Boolean correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set. The Boolean domain is
  represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB15NatSub is Lean's truncated natural subtraction.
  VERINAB15GetBang reproduces Array.get! on integer arrays, returning integer
  zero outside the valid index range. VERINAB15WithIndicesGraph and its
  iota-selected word reproduce a.mapIdx (fun i x => (i, x)): the output has
  the same length and stores exactly the natural index and corresponding
  integer entry at each position.

  VERINAB15AnyConsecutive is the exact truth condition of the source
  withIndices.any scan. It ranges over every mapped pair and preserves the
  Boolean conjunction of the truncated length-minus-one bound with integer
  equality after adding one. VERINAB15ContainsConsecutiveNumbers preserves
  the explicit size-at-most-one false branch and otherwise returns the
  Boolean indicator of that scan, so its output is fixed independently of
  the postcondition and admits no additional results.

  VERINAB15Pre is the source True precondition on typed Array Int inputs.
  VERINAB15Post preserves the source existential natural index, both get!
  calls, integer addition and equality, and equivalence with the Boolean
  result. The proof-valued precondition argument is computationally and
  propositionally unused and is represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB15NatSub VERINAB15GetBang
  VERINAB15WithIndicesGraph VERINAB15WithIndices
  VERINAB15AnyConsecutive
  VERINAB15Pre VERINAB15ContainsConsecutiveNumbers VERINAB15Post
$.

verinab15-nat-sub-syntax
  $a class ( VERINAB15NatSub A B ) $.
verinab15-get-bang-syntax
  $a class ( VERINAB15GetBang A B ) $.
verinab15-with-indices-graph-syntax
  $a wff ( VERINAB15WithIndicesGraph A B ) $.
verinab15-with-indices-syntax
  $a class ( VERINAB15WithIndices A ) $.
verinab15-any-consecutive-syntax
  $a wff ( VERINAB15AnyConsecutive A B ) $.
verinab15-precondition-syntax
  $a wff ( VERINAB15Pre A ) $.
verinab15-program-syntax
  $a class ( VERINAB15ContainsConsecutiveNumbers A ) $.
verinab15-postcondition-syntax
  $a wff ( VERINAB15Post A B ) $.

verinab15-nat-sub-definition $a |- (
  VERINAB15NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab15-get-bang-definition $a |- (
  VERINAB15GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k A B $.

  verinab15-with-indices-graph-definition $a |- (
    VERINAB15WithIndicesGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( NN0 X. ZZ )
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. k e. ( 0 ..^ ( # ` A ) )
        ( B ` k ) = <. k , ( A ` k ) >.
    )
  ) $.
$}

${
  $d y A $.

  verinab15-with-indices-definition $a |- (
    VERINAB15WithIndices A
  ) = (
    iota_ y e. Word ( NN0 X. ZZ )
      ( VERINAB15WithIndicesGraph A y )
  ) $.
$}

${
  $d k A B $.

  verinab15-any-consecutive-definition $a |- (
    VERINAB15AnyConsecutive A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ( NN0 X. ZZ )
    )
    /\
    E. k e. ( 0 ..^ ( # ` B ) )
      (
        (
          1st ` ( B ` k )
        ) < (
          VERINAB15NatSub ( # ` A ) 1
        )
        /\
        (
          ( 2nd ` ( B ` k ) ) + 1
        ) = (
          VERINAB15GetBang
            A
            ( ( 1st ` ( B ` k ) ) + 1 )
        )
      )
  ) $.
$}

verinab15-precondition-definition $a |- (
  VERINAB15Pre A
) <-> (
  A e. Word ZZ
) $.

verinab15-program-definition $a |- (
  VERINAB15ContainsConsecutiveNumbers A
) = if (
  ( # ` A ) <_ 1 ,
  0 ,
  if (
    (
      VERINAB15AnyConsecutive
        A
        ( VERINAB15WithIndices A )
    ) ,
    1 ,
    0
  )
) $.

${
  $d i A B $.

  verinab15-postcondition-definition $a |- (
    VERINAB15Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. { 0 , 1 }
    )
    /\
    (
      E. i e. NN0
        (
          i < ( VERINAB15NatSub ( # ` A ) 1 )
          /\
          (
            ( VERINAB15GetBang A i ) + 1
          ) = (
            VERINAB15GetBang A ( i + 1 )
          )
        )
      <->
      B = 1
    )
  ) $.
$}

verina-basic-15-contains-consecutive-numbers $a |- A. w e. Word ZZ
  (
    ( VERINAB15Pre w )
    ->
    (
      VERINAB15Post
        w
        ( VERINAB15ContainsConsecutiveNumbers w )
    )
  )
$.
