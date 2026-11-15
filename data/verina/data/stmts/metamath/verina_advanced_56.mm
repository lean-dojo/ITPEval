$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_56 (verina__metamath__verina_advanced_56), catalog title
  moveZeroes: the exact filter-and-append program moves every zero in an
  arbitrary finite integer list to the end while preserving the nonzero
  order, together with its complete correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its natural-number
  length, w ` i is zero-based lookup, and 0 ..^ ( # ` w ) is its complete
  index set.

  VERINA56FilterNonzeroGraph and VERINA56FilterZeroGraph select exactly all
  matching source positions in strictly increasing order. Their unique-choice
  functions therefore reproduce the two source List.filter calls, including
  duplicates. VERINA56AppendGraph gives the exact indexed concatenation, and
  VERINA56MoveZeroes explicitly composes these operations, fixing the
  executable result independently of the postcondition.

  VERINA56Count is the recursive countVal helper, expressed equivalently as
  the cardinality of the matching index set. VERINA56Subsequence is equivalent
  to the true result of the source greedy isSubsequence Boolean recursion:
  it gives an order-preserving embedding of every first-list position into
  an equal second-list position. VERINA56IsSubsequence is its exact Boolean
  indicator, with 1 and 0 representing true and false.

  VERINA56DropWhileNonzeroGraph returns the suffix beginning at the first zero,
  or the empty suffix when no zero occurs, exactly as List.dropWhile with the
  nonzero predicate. VERINA56AllZero is the exact Boolean indicator of
  List.all equality-to-zero. VERINA56Pre is the source True precondition on
  typed inputs. VERINA56Post is the four-part source postcondition, and the
  final assertion is the source correctness proposition. Every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINA56FilterNonzeroGraph VERINA56FilterNonzero
  VERINA56FilterZeroGraph VERINA56FilterZero
  VERINA56AppendGraph VERINA56Append
  VERINA56Count
  VERINA56Subsequence VERINA56IsSubsequence
  VERINA56DropWhileNonzeroGraph VERINA56DropWhileNonzero
  VERINA56AllZero
  VERINA56Pre VERINA56MoveZeroes VERINA56Post
$.

verina56-filter-nonzero-graph-syntax
  $a wff ( VERINA56FilterNonzeroGraph A B ) $.
verina56-filter-nonzero-syntax
  $a class ( VERINA56FilterNonzero A ) $.
verina56-filter-zero-graph-syntax
  $a wff ( VERINA56FilterZeroGraph A B ) $.
verina56-filter-zero-syntax
  $a class ( VERINA56FilterZero A ) $.
verina56-append-graph-syntax
  $a wff ( VERINA56AppendGraph A B C ) $.
verina56-append-syntax
  $a class ( VERINA56Append A B ) $.
verina56-count-syntax
  $a class ( VERINA56Count A B ) $.
verina56-subsequence-syntax
  $a wff ( VERINA56Subsequence A B ) $.
verina56-is-subsequence-syntax
  $a class ( VERINA56IsSubsequence A B ) $.
verina56-drop-while-nonzero-graph-syntax
  $a wff ( VERINA56DropWhileNonzeroGraph A B ) $.
verina56-drop-while-nonzero-syntax
  $a class ( VERINA56DropWhileNonzero A ) $.
verina56-all-zero-syntax
  $a class ( VERINA56AllZero A ) $.
verina56-precondition-syntax
  $a wff ( VERINA56Pre A ) $.
verina56-move-zeroes-syntax
  $a class ( VERINA56MoveZeroes A ) $.
verina56-postcondition-syntax
  $a wff ( VERINA56Post A B ) $.

${
  $d i j k p A B $.

  verina56-filter-nonzero-graph-definition $a |- (
    VERINA56FilterNonzeroGraph A B
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

  verina56-filter-nonzero-definition $a |- (
    VERINA56FilterNonzero A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA56FilterNonzeroGraph A y )
  ) $.
$}

${
  $d i j k p A B $.

  verina56-filter-zero-graph-definition $a |- (
    VERINA56FilterZeroGraph A B
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

  verina56-filter-zero-definition $a |- (
    VERINA56FilterZero A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA56FilterZeroGraph A y )
  ) $.
$}

${
  $d i j A B C $.

  verina56-append-graph-definition $a |- (
    VERINA56AppendGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. Word ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( ( # ` A ) + ( # ` B ) )
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          ( C ` i ) = ( A ` i )
        /\
        A. j e. ( 0 ..^ ( # ` B ) )
          ( C ` ( ( # ` A ) + j ) ) = ( B ` j )
      )
    )
  ) $.
$}

${
  $d y A B $.

  verina56-append-definition $a |- (
    VERINA56Append A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINA56AppendGraph A B y )
  ) $.
$}

${
  $d i A B $.

  verina56-count-definition $a |- (
    VERINA56Count A B
  ) = (
    # ` {
      i e. ( 0 ..^ ( # ` A ) )
      |
      ( A ` i ) = B
    }
  ) $.
$}

${
  $d i j k p A B $.

  verina56-subsequence-definition $a |- (
    VERINA56Subsequence A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. p e. Word NN0
      (
        ( # ` p ) = ( # ` A )
        /\
        (
          A. i e. ( 0 ..^ ( # ` A ) )
            (
              ( p ` i ) < ( # ` B )
              /\
              ( A ` i ) = ( B ` ( p ` i ) )
            )
          /\
          A. j e. ( 0 ..^ ( # ` A ) )
            A. k e. ( 0 ..^ ( # ` A ) )
              (
                j < k
                ->
                ( p ` j ) < ( p ` k )
              )
        )
      )
  ) $.
$}

verina56-is-subsequence-definition $a |- (
  VERINA56IsSubsequence A B
) = if (
  ( VERINA56Subsequence A B ) ,
  1 ,
  0
) $.

${
  $d i j k A B $.

  verina56-drop-while-nonzero-graph-definition $a |- (
    VERINA56DropWhileNonzeroGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    E. k e. NN0
      (
        (
          k <_ ( # ` A )
          /\
          ( ( # ` B ) + k ) = ( # ` A )
        )
        /\
        (
          A. j e. ( 0 ..^ ( # ` B ) )
            ( B ` j ) = ( A ` ( k + j ) )
          /\
          (
            (
              (
                k < ( # ` A )
                /\
                ( A ` k ) = 0
              )
              /\
              A. i e. ( 0 ..^ k )
                ( A ` i ) =/= 0
            )
            \/
            (
              k = ( # ` A )
              /\
              A. i e. ( 0 ..^ k )
                ( A ` i ) =/= 0
            )
          )
        )
      )
  ) $.
$}

${
  $d y A $.

  verina56-drop-while-nonzero-definition $a |- (
    VERINA56DropWhileNonzero A
  ) = (
    iota_ y e. Word ZZ
      ( VERINA56DropWhileNonzeroGraph A y )
  ) $.
$}

${
  $d i A $.

  verina56-all-zero-definition $a |- (
    VERINA56AllZero A
  ) = if (
    (
      A e. Word ZZ
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( A ` i ) = 0
    ) ,
    1 ,
    0
  ) $.
$}

verina56-precondition-definition $a |- (
  VERINA56Pre A
) <-> (
  A e. Word ZZ
) $.

verina56-move-zeroes-definition $a |- (
  VERINA56MoveZeroes A
) = (
  VERINA56Append
    ( VERINA56FilterNonzero A )
    ( VERINA56FilterZero A )
) $.

verina56-postcondition-definition $a |- (
  VERINA56Post A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. Word ZZ
  )
  /\
  (
    (
      (
        VERINA56IsSubsequence
          ( VERINA56FilterNonzero A )
          B
      ) = 1
      /\
      (
        VERINA56AllZero
          ( VERINA56DropWhileNonzero B )
      ) = 1
    )
    /\
    (
      ( VERINA56Count A 0 ) = ( VERINA56Count B 0 )
      /\
      ( # ` A ) = ( # ` B )
    )
  )
) $.

verina-advanced-56-move-zeroes
  $a |- A. w e. Word ZZ
    (
      ( VERINA56Pre w )
      ->
      (
        VERINA56Post
          w
          ( VERINA56MoveZeroes w )
      )
    )
  $.
