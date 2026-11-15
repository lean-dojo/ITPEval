$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_35
  (verina__metamath__verina_basic_35), catalog title MoveZeroesToEnd: the
  exact integer-array filter-and-append program moves all zero entries to the
  end while preserving the nonzero order and satisfies the permutation,
  prefix, and suffix correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer arrays and lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete valid-index set. Word concatenation ++ is
  exact finite-list append.

  VERINAB35ToList and VERINAB35ArrayMk are the source Array.toList and
  Array.mk conversions; both are extensionally the identity on this common
  finite-word representation.

  VERINAB35FilterNonzeroGraph and VERINAB35FilterZeroGraph select exactly all
  matching source positions in strictly increasing order. Their unique-choice
  functions therefore reproduce the two stable List.filter calls, including
  duplicates. VERINAB35MoveZeroesToEnd composes those filters, append, and
  Array.mk exactly, fixing the executable result independently of the
  postcondition and admitting no additional outputs.

  VERINAB35IdxOfGraph characterizes List.idxOf exactly: it returns the least
  matching index, or the word length when zero is absent. VERINAB35TakeGraph
  and VERINAB35DropGraph reproduce List.take and List.drop for every natural
  index, including clipping at the word length. VERINAB35Perm is List.isPerm,
  represented equivalently by equality of every integer's multiplicity.

  VERINAB35Pre is the source True precondition on typed Array Int inputs.
  VERINAB35Post preserves the source permutation clause and the exact take and
  drop equalities at the first result-zero index. The proof-valued precondition
  arguments to the implementation and postcondition are computationally and
  propositionally unused and are represented by the explicit antecedent in
  the final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB35ToList VERINAB35ArrayMk
  VERINAB35FilterNonzeroGraph VERINAB35FilterNonzero
  VERINAB35FilterZeroGraph VERINAB35FilterZero
  VERINAB35IdxOfGraph VERINAB35IdxOf
  VERINAB35NatMin
  VERINAB35TakeGraph VERINAB35Take
  VERINAB35DropGraph VERINAB35Drop
  VERINAB35Perm
  VERINAB35Pre VERINAB35MoveZeroesToEnd VERINAB35Post
$.

verinab35-to-list-syntax
  $a class ( VERINAB35ToList A ) $.
verinab35-array-mk-syntax
  $a class ( VERINAB35ArrayMk A ) $.
verinab35-filter-nonzero-graph-syntax
  $a wff ( VERINAB35FilterNonzeroGraph A B ) $.
verinab35-filter-nonzero-syntax
  $a class ( VERINAB35FilterNonzero A ) $.
verinab35-filter-zero-graph-syntax
  $a wff ( VERINAB35FilterZeroGraph A B ) $.
verinab35-filter-zero-syntax
  $a class ( VERINAB35FilterZero A ) $.
verinab35-idx-of-graph-syntax
  $a wff ( VERINAB35IdxOfGraph A B C ) $.
verinab35-idx-of-syntax
  $a class ( VERINAB35IdxOf A B ) $.
verinab35-nat-min-syntax
  $a class ( VERINAB35NatMin A B ) $.
verinab35-take-graph-syntax
  $a wff ( VERINAB35TakeGraph A B C ) $.
verinab35-take-syntax
  $a class ( VERINAB35Take A B ) $.
verinab35-drop-graph-syntax
  $a wff ( VERINAB35DropGraph A B C ) $.
verinab35-drop-syntax
  $a class ( VERINAB35Drop A B ) $.
verinab35-permutation-syntax
  $a wff ( VERINAB35Perm A B ) $.
verinab35-precondition-syntax
  $a wff ( VERINAB35Pre A ) $.
verinab35-program-syntax
  $a class ( VERINAB35MoveZeroesToEnd A ) $.
verinab35-postcondition-syntax
  $a wff ( VERINAB35Post A B ) $.

verinab35-to-list-definition $a |- (
  VERINAB35ToList A
) = A $.

verinab35-array-mk-definition $a |- (
  VERINAB35ArrayMk A
) = A $.

${
  $d i j k p A B $.

  verinab35-filter-nonzero-graph-definition $a |- (
    VERINAB35FilterNonzeroGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` B )
        /\
        (
          A. j e. ( 0 ..^ ( # ` B ) )
            (
              (
                ( p ` j ) < ( # ` A )
                /\
                ( A ` ( p ` j ) ) =/= 0
              )
              /\
              ( B ` j ) = ( A ` ( p ` j ) )
            )
          /\
          (
            A. j e. ( 0 ..^ ( # ` B ) )
              A. k e. ( 0 ..^ ( # ` B ) )
                (
                  j < k
                  ->
                  ( p ` j ) < ( p ` k )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( A ` i ) =/= 0
                ->
                E. j e. ( 0 ..^ ( # ` B ) )
                  ( p ` j ) = i
              )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab35-filter-nonzero-definition $a |- (
    VERINAB35FilterNonzero A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB35FilterNonzeroGraph A y )
  ) $.
$}

${
  $d i j k p A B $.

  verinab35-filter-zero-graph-definition $a |- (
    VERINAB35FilterZeroGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` B )
        /\
        (
          A. j e. ( 0 ..^ ( # ` B ) )
            (
              (
                ( p ` j ) < ( # ` A )
                /\
                ( A ` ( p ` j ) ) = 0
              )
              /\
              ( B ` j ) = ( A ` ( p ` j ) )
            )
          /\
          (
            A. j e. ( 0 ..^ ( # ` B ) )
              A. k e. ( 0 ..^ ( # ` B ) )
                (
                  j < k
                  ->
                  ( p ` j ) < ( p ` k )
                )
            /\
            A. i e. ( 0 ..^ ( # ` A ) )
              (
                ( A ` i ) = 0
                ->
                E. j e. ( 0 ..^ ( # ` B ) )
                  ( p ` j ) = i
              )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verinab35-filter-zero-definition $a |- (
    VERINAB35FilterZero A
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB35FilterZeroGraph A y )
  ) $.
$}

${
  $d i j A B C $.

  verinab35-idx-of-graph-definition $a |- (
    VERINAB35IdxOfGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. NN0
    )
    /\
    (
      (
        (
          C e. ( 0 ..^ ( # ` A ) )
          /\
          ( A ` C ) = B
        )
        /\
        A. j e. ( 0 ..^ C )
          ( A ` j ) =/= B
      )
      \/
      (
        C = ( # ` A )
        /\
        A. i e. ( 0 ..^ ( # ` A ) )
          ( A ` i ) =/= B
      )
    )
  ) $.
$}

${
  $d y A B $.

  verinab35-idx-of-definition $a |- (
    VERINAB35IdxOf A B
  ) = (
    iota_ y e. NN0
      ( VERINAB35IdxOfGraph A B y )
  ) $.
$}

verinab35-nat-min-definition $a |- (
  VERINAB35NatMin A B
) = if (
  A < B ,
  A ,
  B
) $.

${
  $d i A B C $.

  verinab35-take-graph-definition $a |- (
    VERINAB35TakeGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = (
        VERINAB35NatMin B ( # ` A )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        ( C ` i ) = ( A ` i )
    )
  ) $.
$}

${
  $d y A B $.

  verinab35-take-definition $a |- (
    VERINAB35Take A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB35TakeGraph A B y )
  ) $.
$}

${
  $d i A B C $.

  verinab35-drop-graph-definition $a |- (
    VERINAB35DropGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = (
        ( # ` A ) - (
          VERINAB35NatMin B ( # ` A )
        )
      )
      /\
      A. i e. ( 0 ..^ ( # ` C ) )
        (
          C ` i
        ) = (
          A ` (
            ( VERINAB35NatMin B ( # ` A ) ) + i
          )
        )
    )
  ) $.
$}

${
  $d y A B $.

  verinab35-drop-definition $a |- (
    VERINAB35Drop A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB35DropGraph A B y )
  ) $.
$}

${
  $d i j x A B $.

  verinab35-permutation-definition $a |- (
    VERINAB35Perm A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    A. x e. ZZ
      (
        # ` {
          i e. ( 0 ..^ ( # ` A ) )
          |
          ( A ` i ) = x
        }
      ) = (
        # ` {
          j e. ( 0 ..^ ( # ` B ) )
          |
          ( B ` j ) = x
        }
      )
  ) $.
$}

verinab35-precondition-definition $a |- (
  VERINAB35Pre A
) <-> (
  A e. Word ZZ
) $.

verinab35-program-definition $a |- (
  VERINAB35MoveZeroesToEnd A
) = (
  VERINAB35ArrayMk (
    (
      VERINAB35FilterNonzero
        ( VERINAB35ToList A )
    )
    ++
    (
      VERINAB35FilterZero
        ( VERINAB35ToList A )
    )
  )
) $.

verinab35-postcondition-definition $a |- (
  VERINAB35Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    (
      VERINAB35Perm
        ( VERINAB35ToList B )
        ( VERINAB35ToList A )
    )
    /\
    (
      (
        VERINAB35Take
          ( VERINAB35ToList B )
          (
            VERINAB35IdxOf
              ( VERINAB35ToList B )
              0
          )
      ) = (
        VERINAB35FilterNonzero
          ( VERINAB35ToList A )
      )
      /\
      (
        VERINAB35Drop
          ( VERINAB35ToList B )
          (
            VERINAB35IdxOf
              ( VERINAB35ToList B )
              0
          )
      ) = (
        VERINAB35FilterZero
          ( VERINAB35ToList A )
      )
    )
  )
) $.

verina-basic-35-move-zeroes-to-end
  $a |- A. w e. Word ZZ
    (
      ( VERINAB35Pre w )
      ->
      (
        VERINAB35Post
          w
          ( VERINAB35MoveZeroesToEnd w )
      )
    )
  $.
