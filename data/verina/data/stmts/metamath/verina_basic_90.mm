$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_90
  (verina__metamath__verina_basic_90), catalog title SlopeSearch: the exact
  fuel-bounded executable slope search of a rectangular integer matrix,
  under row-wise and column-wise nondecreasing-order assumptions, satisfies
  its found-position or absent-key correctness contract. This file contains
  no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains.
  Word ZZ is exactly the type of arbitrary finite integer arrays, and
  Word ( Word ZZ ) is exactly the type of arbitrary finite arrays of such
  arrays. For a word w, # ` w is its natural-number size, w ` i is
  zero-based lookup, and 0 ..^ ( # ` w ) is its complete valid-index set.
  The product ZZ X. ZZ, ordered-pair constructor <. A , B >., and projections
  1st and 2nd represent the source result type Int x Int.

  VERINAB90NatSub is Lean's truncated natural subtraction, and
  VERINAB90ToNat is Lean Int.toNat. VERINAB90GetBang reproduces get! on an
  integer row with default zero. VERINAB90GetRowBang reproduces get! on the
  outer array with the default empty integer array. Consequently
  VERINAB90Get2d is exactly the source helper get2d, including both Int.toNat
  conversions and both inhabited defaults. VERINAB90Cols preserves the
  source rows-positive conditional used to compute cols.

  VERINAB90PairwiseSizeEq is List.Pairwise equality of row sizes.
  VERINAB90PairwiseLE is List.Pairwise integer nondecreasing order.
  VERINAB90ColumnsPairwiseLE applies that same relation to each column word
  produced by mapping zero-default row lookup over the matrix.
  VERINAB90Pre preserves the nonempty outer array, nonempty first row,
  pairwise-equal row sizes, every row's sortedness, every first-row column's
  sortedness, and the typed but otherwise unrestricted integer key.

  VERINAB90AuxGraph is the exact operational graph of the source local aux
  recursion. Its trace contains the initial (m,n) state and one state for
  each unit of natural fuel. At every positive-fuel step it first freezes on
  the source out-of-bounds test, next freezes on equality with the key, then
  increments m when the entry is below the key and otherwise decrements n.
  A successful result is admitted exactly when equality is observed at a
  state whose corresponding recursive call still has positive fuel; if no
  such state exists, including when equality is first reached only after the
  final transition, the result is (-1,-1). Thus the graph permits exactly
  the source computation and no additional output. VERINAB90Aux selects that
  unique result, and VERINAB90SlopeSearch starts at row zero and the
  truncated predecessor of cols with fuel rows + cols.

  VERINAB90NoKey is the nested Array.all absence test. VERINAB90Post preserves
  the source disjunction: either both result components are valid matrix
  indices containing the key, or both are -1 and every matrix entry differs
  from the key. The proof-valued precondition arguments have no computational
  or propositional effect beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this artifact adds no $p
  declaration.
$)

$c
  VERINAB90NatSub VERINAB90ToNat
  VERINAB90GetBang VERINAB90GetRowBang VERINAB90Get2d VERINAB90Cols
  VERINAB90PairwiseSizeEq VERINAB90PairwiseLE
  VERINAB90ColumnsPairwiseLE VERINAB90Pre
  VERINAB90AuxGraph VERINAB90Aux VERINAB90SlopeSearch
  VERINAB90NoKey VERINAB90Post
$.

verinab90-nat-sub-syntax
  $a class ( VERINAB90NatSub A B ) $.
verinab90-to-nat-syntax
  $a class ( VERINAB90ToNat A ) $.
verinab90-get-bang-syntax
  $a class ( VERINAB90GetBang A B ) $.
verinab90-get-row-bang-syntax
  $a class ( VERINAB90GetRowBang A B ) $.
verinab90-get2d-syntax
  $a class ( VERINAB90Get2d A B C ) $.
verinab90-cols-syntax
  $a class ( VERINAB90Cols A ) $.
verinab90-pairwise-size-eq-syntax
  $a wff ( VERINAB90PairwiseSizeEq A ) $.
verinab90-pairwise-le-syntax
  $a wff ( VERINAB90PairwiseLE A ) $.
verinab90-columns-pairwise-le-syntax
  $a wff ( VERINAB90ColumnsPairwiseLE A ) $.
verinab90-precondition-syntax
  $a wff ( VERINAB90Pre A B ) $.
verinab90-aux-graph-syntax
  $a wff ( VERINAB90AuxGraph A B C D E F ) $.
verinab90-aux-syntax
  $a class ( VERINAB90Aux A B C D E ) $.
verinab90-program-syntax
  $a class ( VERINAB90SlopeSearch A B ) $.
verinab90-no-key-syntax
  $a wff ( VERINAB90NoKey A B ) $.
verinab90-postcondition-syntax
  $a wff ( VERINAB90Post A B C ) $.

verinab90-nat-sub-definition $a |- (
  VERINAB90NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab90-to-nat-definition $a |- (
  VERINAB90ToNat A
) = if (
  A < 0 ,
  0 ,
  A
) $.

verinab90-get-bang-definition $a |- (
  VERINAB90GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab90-get-row-bang-definition $a |- (
  VERINAB90GetRowBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  (/)
) $.

verinab90-get2d-definition $a |- (
  VERINAB90Get2d A B C
) = (
  VERINAB90GetBang
    (
      VERINAB90GetRowBang
        A
        ( VERINAB90ToNat B )
    )
    ( VERINAB90ToNat C )
) $.

verinab90-cols-definition $a |- (
  VERINAB90Cols A
) = if (
  0 < ( # ` A ) ,
  ( # ` ( VERINAB90GetRowBang A 0 ) ) ,
  0
) $.

${
  $d i j A $.

  verinab90-pairwise-size-eq-definition $a |- (
    VERINAB90PairwiseSizeEq A
  ) <-> (
    A e. Word ( Word ZZ )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( # ` ( A ` i ) ) = ( # ` ( A ` j ) )
        )
  ) $.
$}

${
  $d i j A $.

  verinab90-pairwise-le-definition $a |- (
    VERINAB90PairwiseLE A
  ) <-> (
    A e. Word ZZ
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` A ) )
        (
          i < j
          ->
          ( A ` i ) <_ ( A ` j )
        )
  ) $.
$}

${
  $d c i j A $.

  verinab90-columns-pairwise-le-definition $a |- (
    VERINAB90ColumnsPairwiseLE A
  ) <-> (
    A e. Word ( Word ZZ )
    /\
    A. c e. (
      0 ..^ ( # ` ( VERINAB90GetRowBang A 0 ) )
    )
      A. i e. ( 0 ..^ ( # ` A ) )
        A. j e. ( 0 ..^ ( # ` A ) )
          (
            i < j
            ->
            (
              VERINAB90GetBang ( A ` i ) c
            ) <_ (
              VERINAB90GetBang ( A ` j ) c
            )
          )
  ) $.
$}

${
  $d i A B $.

  verinab90-precondition-definition $a |- (
    VERINAB90Pre A B
  ) <-> (
    (
      A e. Word ( Word ZZ )
      /\
      B e. ZZ
    )
    /\
    (
      0 < ( # ` A )
      /\
      (
        0 < ( # ` ( VERINAB90GetRowBang A 0 ) )
        /\
        (
          ( VERINAB90PairwiseSizeEq A )
          /\
          (
            A. i e. ( 0 ..^ ( # ` A ) )
              ( VERINAB90PairwiseLE ( A ` i ) )
            /\
            ( VERINAB90ColumnsPairwiseLE A )
          )
        )
      )
    )
  ) $.
$}

${
  $d k t A B C D E F $.

  verinab90-aux-graph-definition $a |- (
    VERINAB90AuxGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            A e. Word ( Word ZZ )
            /\
            B e. ZZ
          )
          /\
          (
            C e. ZZ
            /\
            D e. ZZ
          )
        )
        /\
        E e. NN0
      )
      /\
      F e. ( ZZ X. ZZ )
    )
    /\
    E. t e. Word ( ZZ X. ZZ )
      (
        (
          ( # ` t ) = ( E + 1 )
          /\
          ( t ` 0 ) = <. C , D >.
        )
        /\
        (
          A. k e. ( 0 ..^ E )
            (
              t ` ( k + 1 )
            ) = if (
              (
                ( # ` A ) <_ ( 1st ` ( t ` k ) )
                \/
                ( 2nd ` ( t ` k ) ) < 0
              ) ,
              ( t ` k ) ,
              if (
                (
                  VERINAB90Get2d
                    A
                    ( 1st ` ( t ` k ) )
                    ( 2nd ` ( t ` k ) )
                ) = B ,
                ( t ` k ) ,
                if (
                  (
                    VERINAB90Get2d
                      A
                      ( 1st ` ( t ` k ) )
                      ( 2nd ` ( t ` k ) )
                  ) < B ,
                  <.
                    ( ( 1st ` ( t ` k ) ) + 1 ) ,
                    ( 2nd ` ( t ` k ) )
                  >. ,
                  <.
                    ( 1st ` ( t ` k ) ) ,
                    ( ( 2nd ` ( t ` k ) ) - 1 )
                  >.
                )
              )
            )
          /\
          (
            E. k e. ( 0 ..^ E )
              (
                (
                  (
                    ( 1st ` ( t ` k ) ) < ( # ` A )
                    /\
                    0 <_ ( 2nd ` ( t ` k ) )
                  )
                  /\
                  (
                    VERINAB90Get2d
                      A
                      ( 1st ` ( t ` k ) )
                      ( 2nd ` ( t ` k ) )
                  ) = B
                )
                /\
                F = ( t ` k )
              )
            \/
            (
              -.
              E. k e. ( 0 ..^ E )
                (
                  (
                    ( 1st ` ( t ` k ) ) < ( # ` A )
                    /\
                    0 <_ ( 2nd ` ( t ` k ) )
                  )
                  /\
                  (
                    VERINAB90Get2d
                      A
                      ( 1st ` ( t ` k ) )
                      ( 2nd ` ( t ` k ) )
                  ) = B
                )
              /\
              F = <. ( -u 1 ) , ( -u 1 ) >.
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab90-aux-definition $a |- (
    VERINAB90Aux A B C D E
  ) = (
    iota_ y e. ( ZZ X. ZZ )
      (
        VERINAB90AuxGraph
          A B C D E y
      )
  ) $.
$}

verinab90-program-definition $a |- (
  VERINAB90SlopeSearch A B
) = (
  VERINAB90Aux
    A
    B
    0
    ( VERINAB90NatSub ( VERINAB90Cols A ) 1 )
    ( ( # ` A ) + ( VERINAB90Cols A ) )
) $.

${
  $d i j A B $.

  verinab90-no-key-definition $a |- (
    VERINAB90NoKey A B
  ) <-> (
    (
      A e. Word ( Word ZZ )
      /\
      B e. ZZ
    )
    /\
    A. i e. ( 0 ..^ ( # ` A ) )
      A. j e. ( 0 ..^ ( # ` ( A ` i ) ) )
        ( ( A ` i ) ` j ) =/= B
  ) $.
$}

verinab90-postcondition-definition $a |- (
  VERINAB90Post A B C
) <-> (
  (
    (
      A e. Word ( Word ZZ )
      /\
      B e. ZZ
    )
    /\
    C e. ( ZZ X. ZZ )
  )
  /\
  (
    (
      (
        0 <_ ( 1st ` C )
        /\
        ( 1st ` C ) < ( # ` A )
      )
      /\
      (
        0 <_ ( 2nd ` C )
        /\
        (
          ( 2nd ` C ) < (
            # ` ( VERINAB90GetRowBang A 0 )
          )
          /\
          (
            VERINAB90Get2d
              A
              ( 1st ` C )
              ( 2nd ` C )
          ) = B
        )
      )
    )
    \/
    (
      (
        ( 1st ` C ) = ( -u 1 )
        /\
        ( 2nd ` C ) = ( -u 1 )
      )
      /\
      ( VERINAB90NoKey A B )
    )
  )
) $.

${
  $d a z $.

  verina-basic-90-slope-search $a |-
    A. a e. Word ( Word ZZ )
      A. z e. ZZ
        (
          ( VERINAB90Pre a z )
          ->
          (
            VERINAB90Post
              a
              z
              ( VERINAB90SlopeSearch a z )
          )
        )
  $.
$}
