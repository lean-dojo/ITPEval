$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_60 (verina__metamath__verina_advanced_60), catalog title
  partitionEvensOdds: the exact executable recursive partition of an
  arbitrary finite natural-number list into its even and odd entries in
  source order, together with its complete correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's NN0 is the full natural-number domain, and Word NN0 is exactly the
  type of arbitrary finite natural-number lists. For a word w, # ` w is its
  natural-number length, w ` i is zero-based lookup, and
  0 ..^ ( # ` w ) is its complete index set.

  VERINA60Even and VERINA60Odd are exactly the source remainder tests
  n % 2 == 0 and n % 2 == 1. VERINA60FilterEvenGraph and
  VERINA60FilterOddGraph retain precisely all matching input positions in
  strictly increasing order, including repeated values. Their unique-choice
  functions therefore reproduce the two stable List.filter computations.

  VERINA60HelperGraph returns the pair of those two filtered words, and
  VERINA60Helper selects that unique pair. This is exactly the source local
  recursive helper: on the empty word both filters are empty, while on
  x :: xs the matching filter is x :: filter xs and the other is filter xs.
  Thus the graph has the same base case and both recursive branches as the
  Lean helper. VERINA60PartitionEvensOdds is the source public executable
  implementation, so its result is fixed independently of the postcondition.

  VERINA60AppendGraph is exact word concatenation. VERINA60Pre is the source
  True precondition on typed inputs. VERINA60Post reproduces the equality of
  result concatenation with the concatenated even and odd source filters,
  followed by the source List.all even and List.all odd clauses. The
  proof-valued precondition argument is computationally and propositionally
  unused and is represented by the explicit antecedent of the final
  correctness assertion. Every earlier $a is syntax or a faithful
  definition, and this database has no $p declaration.
$)

$c
  VERINA60Even VERINA60Odd
  VERINA60FilterEvenGraph VERINA60FilterEven
  VERINA60FilterOddGraph VERINA60FilterOdd
  VERINA60HelperGraph VERINA60Helper VERINA60PartitionEvensOdds
  VERINA60AppendGraph VERINA60Append
  VERINA60Pre VERINA60Post
$.

verina60-even-syntax
  $a wff ( VERINA60Even A ) $.
verina60-odd-syntax
  $a wff ( VERINA60Odd A ) $.
verina60-filter-even-graph-syntax
  $a wff ( VERINA60FilterEvenGraph A B ) $.
verina60-filter-even-syntax
  $a class ( VERINA60FilterEven A ) $.
verina60-filter-odd-graph-syntax
  $a wff ( VERINA60FilterOddGraph A B ) $.
verina60-filter-odd-syntax
  $a class ( VERINA60FilterOdd A ) $.
verina60-helper-graph-syntax
  $a wff ( VERINA60HelperGraph A B ) $.
verina60-helper-syntax
  $a class ( VERINA60Helper A ) $.
verina60-program-syntax
  $a class ( VERINA60PartitionEvensOdds A ) $.
verina60-append-graph-syntax
  $a wff ( VERINA60AppendGraph A B C ) $.
verina60-append-syntax
  $a class ( VERINA60Append A B ) $.
verina60-precondition-syntax
  $a wff ( VERINA60Pre A ) $.
verina60-postcondition-syntax
  $a wff ( VERINA60Post A B ) $.

verina60-even-definition $a |- (
  VERINA60Even A
) <-> (
  A e. NN0
  /\
  ( A mod 2 ) = 0
) $.

verina60-odd-definition $a |- (
  VERINA60Odd A
) <-> (
  A e. NN0
  /\
  ( A mod 2 ) = 1
) $.

${
  $d i j k p A B $.

  verina60-filter-even-graph-definition $a |- (
    VERINA60FilterEvenGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
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
                ( VERINA60Even ( A ` ( p ` j ) ) )
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
                ( VERINA60Even ( A ` i ) )
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

  verina60-filter-even-definition $a |- (
    VERINA60FilterEven A
  ) = (
    iota_ y e. Word NN0
      ( VERINA60FilterEvenGraph A y )
  ) $.
$}

${
  $d i j k p A B $.

  verina60-filter-odd-graph-definition $a |- (
    VERINA60FilterOddGraph A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. Word NN0
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
                ( VERINA60Odd ( A ` ( p ` j ) ) )
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
                ( VERINA60Odd ( A ` i ) )
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

  verina60-filter-odd-definition $a |- (
    VERINA60FilterOdd A
  ) = (
    iota_ y e. Word NN0
      ( VERINA60FilterOddGraph A y )
  ) $.
$}

verina60-helper-graph-definition $a |- (
  VERINA60HelperGraph A B
) <-> (
  (
    A e. Word NN0
    /\
    B e. ( Word NN0 X. Word NN0 )
  )
  /\
  B = <.
    ( VERINA60FilterEven A ) ,
    ( VERINA60FilterOdd A )
  >.
) $.

${
  $d y A $.

  verina60-helper-definition $a |- (
    VERINA60Helper A
  ) = (
    iota_ y e. ( Word NN0 X. Word NN0 )
      ( VERINA60HelperGraph A y )
  ) $.
$}

verina60-program-definition $a |- (
  VERINA60PartitionEvensOdds A
) = (
  VERINA60Helper A
) $.

${
  $d i j A B C $.

  verina60-append-graph-definition $a |- (
    VERINA60AppendGraph A B C
  ) <-> (
    (
      (
        A e. Word NN0
        /\
        B e. Word NN0
      )
      /\
      C e. Word NN0
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

  verina60-append-definition $a |- (
    VERINA60Append A B
  ) = (
    iota_ y e. Word NN0
      ( VERINA60AppendGraph A B y )
  ) $.
$}

verina60-precondition-definition $a |- (
  VERINA60Pre A
) <-> (
  A e. Word NN0
) $.

${
  $d i j A B $.

  verina60-postcondition-definition $a |- (
    VERINA60Post A B
  ) <-> (
    (
      A e. Word NN0
      /\
      B e. ( Word NN0 X. Word NN0 )
    )
    /\
    (
      (
        VERINA60Append
          ( 1st ` B )
          ( 2nd ` B )
      ) = (
        VERINA60Append
          ( VERINA60FilterEven A )
          ( VERINA60FilterOdd A )
      )
      /\
      (
        A. i e. ( 0 ..^ ( # ` ( 1st ` B ) ) )
          ( VERINA60Even ( ( 1st ` B ) ` i ) )
        /\
        A. j e. ( 0 ..^ ( # ` ( 2nd ` B ) ) )
          ( VERINA60Odd ( ( 2nd ` B ) ` j ) )
      )
    )
  ) $.
$}

verina-advanced-60-partition-evens-odds $a |- A. w e. Word NN0
  (
    ( VERINA60Pre w )
    ->
    (
      VERINA60Post
        w
        ( VERINA60PartitionEvensOdds w )
    )
  )
$.
