$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_49
  (verina__metamath__verina_basic_49), catalog title findFirstOdd: the exact
  executable indexed-list search returns the least natural index containing
  an odd integer in a nonempty finite array, or none when no such index
  exists, and satisfies its complete correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and lists.
  For a word w, # ` w is its natural-number length, w ` i is zero-based
  lookup, and 0 ..^ ( # ` w ) is its complete valid-index set. The Boolean
  domain is represented by { 0 , 1 }, with false = 0 and true = 1.

  VERINAB49IsOdd is exactly the source Boolean helper x % 2 != 0. For the
  positive divisor two, SetMM integer remainder agrees with Lean's
  nonnegative Int remainder on every integer. VERINAB49GetBang reproduces
  Lean Array.get! on integer arrays, including its inhabited default zero
  outside the array. VERINAB49ToList is the source Array.toList conversion
  extensionally.

  VERINAB49Pair is Int x Nat. VERINAB49IndexedGraph and VERINAB49Indexed
  construct exactly a.toList.zipIdx: the output has the same length and its
  entry at each valid position i is the pair (a[i], i).
  VERINAB49FirstMatch is the unique least indexed-list position whose value
  is odd. VERINAB49FindPair returns the pair at that position when one
  exists, and none otherwise, exactly reproducing the source List.find?.

  VERINAB49None, VERINAB49Some, VERINAB49OptionPair, and
  VERINAB49OptionNat are disjoint tagged encodings of the two source option
  types. VERINAB49FoundValue extracts the pair from a successful find, and
  VERINAB49MapIndex reproduces Option.map (fun (_, i) => i).
  VERINAB49FindFirstOdd composes these exact source operations, so its output
  is fixed independently of the postcondition and admits no additional
  results.

  VERINAB49Pre is exactly the positive-size precondition on an Array Int.
  VERINAB49Post preserves both branches of the source option match: some idx
  requires an in-bounds odd entry and no odd entry at an earlier natural
  index, while none requires that every valid array entry is not odd. The
  proof-valued precondition arguments to the implementation and
  postcondition have no computational or propositional effect beyond the
  explicit antecedent in the final correctness assertion. Every earlier $a
  is syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB49IsOdd VERINAB49GetBang VERINAB49ToList
  VERINAB49Pair VERINAB49IndexedGraph VERINAB49Indexed
  VERINAB49None VERINAB49Some VERINAB49OptionPair VERINAB49OptionNat
  VERINAB49FirstMatch VERINAB49FindPair
  VERINAB49FoundValue VERINAB49MapIndex
  VERINAB49Pre VERINAB49FindFirstOdd VERINAB49Post
$.

verinab49-is-odd-syntax
  $a class ( VERINAB49IsOdd A ) $.
verinab49-get-bang-syntax
  $a class ( VERINAB49GetBang A B ) $.
verinab49-to-list-syntax
  $a class ( VERINAB49ToList A ) $.
verinab49-pair-syntax
  $a class VERINAB49Pair $.
verinab49-indexed-graph-syntax
  $a wff ( VERINAB49IndexedGraph A B ) $.
verinab49-indexed-syntax
  $a class ( VERINAB49Indexed A ) $.
verinab49-none-syntax
  $a class VERINAB49None $.
verinab49-some-syntax
  $a class ( VERINAB49Some A ) $.
verinab49-option-pair-syntax
  $a class VERINAB49OptionPair $.
verinab49-option-nat-syntax
  $a class VERINAB49OptionNat $.
verinab49-first-match-syntax
  $a class ( VERINAB49FirstMatch A ) $.
verinab49-find-pair-syntax
  $a class ( VERINAB49FindPair A ) $.
verinab49-found-value-syntax
  $a class ( VERINAB49FoundValue A ) $.
verinab49-map-index-syntax
  $a class ( VERINAB49MapIndex A ) $.
verinab49-precondition-syntax
  $a wff ( VERINAB49Pre A ) $.
verinab49-program-syntax
  $a class ( VERINAB49FindFirstOdd A ) $.
verinab49-postcondition-syntax
  $a wff ( VERINAB49Post A B ) $.

verinab49-is-odd-definition $a |- (
  VERINAB49IsOdd A
) = if (
  ( A mod 2 ) =/= 0 ,
  1 ,
  0
) $.

verinab49-get-bang-definition $a |- (
  VERINAB49GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab49-to-list-definition $a |- (
  VERINAB49ToList A
) = A $.

verinab49-pair-definition $a |- VERINAB49Pair = (
  ZZ X. NN0
) $.

${
  $d i A B $.

  verinab49-indexed-graph-definition $a |- (
    VERINAB49IndexedGraph A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word VERINAB49Pair
    )
    /\
    (
      ( # ` B ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( B ` i ) = <. ( A ` i ) , i >.
    )
  ) $.
$}

${
  $d y A $.

  verinab49-indexed-definition $a |- (
    VERINAB49Indexed A
  ) = (
    iota_ y e. Word VERINAB49Pair
      ( VERINAB49IndexedGraph A y )
  ) $.
$}

verinab49-none-definition $a |- VERINAB49None = (/) $.

verinab49-some-definition $a |- (
  VERINAB49Some A
) = <. 1 , A >. $.

${
  $d p x $.

  verinab49-option-pair-definition $a |- VERINAB49OptionPair =
    { x |
      (
        x = VERINAB49None
        \/
        E. p e. VERINAB49Pair x = ( VERINAB49Some p )
      )
    } $.
$}

${
  $d n x $.

  verinab49-option-nat-definition $a |- VERINAB49OptionNat =
    { x |
      (
        x = VERINAB49None
        \/
        E. n e. NN0 x = ( VERINAB49Some n )
      )
    } $.
$}

${
  $d i j A $.

  verinab49-first-match-definition $a |- (
    VERINAB49FirstMatch A
  ) = (
    iota_ i e. ( 0 ..^ ( # ` A ) )
      (
        (
          VERINAB49IsOdd
            ( 1st ` ( A ` i ) )
        ) = 1
        /\
        A. j e. ( 0 ..^ i )
          (
            VERINAB49IsOdd
              ( 1st ` ( A ` j ) )
          ) = 0
      )
  ) $.
$}

${
  $d i A $.

  verinab49-find-pair-definition $a |- (
    VERINAB49FindPair A
  ) = if (
    E. i e. ( 0 ..^ ( # ` A ) )
      (
        VERINAB49IsOdd
          ( 1st ` ( A ` i ) )
      ) = 1 ,
    (
      VERINAB49Some
        ( A ` ( VERINAB49FirstMatch A ) )
    ) ,
    VERINAB49None
  ) $.
$}

${
  $d p A $.

  verinab49-found-value-definition $a |- (
    VERINAB49FoundValue A
  ) = (
    iota_ p e. VERINAB49Pair
      A = ( VERINAB49Some p )
  ) $.
$}

verinab49-map-index-definition $a |- (
  VERINAB49MapIndex A
) = if (
  A = VERINAB49None ,
  VERINAB49None ,
  (
    VERINAB49Some
      ( 2nd ` ( VERINAB49FoundValue A ) )
  )
) $.

verinab49-precondition-definition $a |- (
  VERINAB49Pre A
) <-> (
  (
    A e. Word ZZ
    /\
    0 < ( # ` A )
  )
) $.

verinab49-program-definition $a |- (
  VERINAB49FindFirstOdd A
) = (
  VERINAB49MapIndex
    (
      VERINAB49FindPair
        (
          VERINAB49Indexed
            ( VERINAB49ToList A )
        )
    )
) $.

${
  $d i j A B $.

  verinab49-postcondition-definition $a |- (
    VERINAB49Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. VERINAB49OptionNat
    )
    /\
    (
      (
        B = VERINAB49None
        /\
        A. i e. NN0
          (
            i < ( # ` A )
            ->
            (
              VERINAB49IsOdd
                ( VERINAB49GetBang A i )
            ) = 0
          )
      )
      \/
      E. i e. NN0
        (
          B = ( VERINAB49Some i )
          /\
          (
            (
              i < ( # ` A )
              /\
              (
                VERINAB49IsOdd
                  ( VERINAB49GetBang A i )
              ) = 1
            )
            /\
            A. j e. NN0
              (
                j < i
                ->
                (
                  VERINAB49IsOdd
                    ( VERINAB49GetBang A j )
                ) = 0
              )
          )
        )
    )
  ) $.
$}

verina-basic-49-find-first-odd $a |- A. w e. Word ZZ
  (
    ( VERINAB49Pre w )
    ->
    (
      VERINAB49Post
        w
        ( VERINAB49FindFirstOdd w )
    )
  )
$.
