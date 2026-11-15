$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_51
  (verina__metamath__verina_basic_51), catalog title BinarySearch: the exact
  executable recursive lower-bound binary search on a nondecreasing finite
  integer array returns its insertion index and satisfies the strict-prefix
  and greater-or-equal-suffix correctness contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays and their
  toList conversions. For a word w, # ` w is its natural-number length,
  w ` i is zero-based lookup, 0 ..^ n is { 0, ..., n - 1 }, and m ..^ n is
  the half-open natural interval from m through n - 1.

  VERINAB51ToList is Array.toList, extensionally the identity on this finite
  word representation. VERINAB51GetBang reproduces Lean Array.get! on integer
  arrays, including its inhabited default value zero outside the array.
  VERINAB51PairwiseLE is exactly List.Pairwise (fun x y => x <= y), expressed
  over every earlier/later index pair. VERINAB51Pre preserves that sortedness
  precondition together with both source input types.

  VERINAB51LoopGraph is the complete finite execution trace of the source
  binarySearchLoop for every typed array, integer key, and natural lo and hi.
  Every nonterminal state has lo < hi, uses floor((lo + hi) / 2), and takes
  exactly the source branch determined by get! at that midpoint. Its final
  state has hi <= lo and returns lo, exactly matching the source else branch.
  VERINAB51Loop selects the unique natural result fixed by this trace, and
  VERINAB51BinarySearch invokes it with lo zero and hi equal to the array
  size. Thus the executable output is fixed independently of the postcondition
  and the graph admits no extra outputs, including for unsorted arrays or
  arbitrary natural helper bounds.

  VERINAB51Post is bidirectionally equivalent to the source Array.take/all and
  Array.drop/all conjunction. Its first conjunct requires result <= size; under
  that bound, take result has exactly indices below result and drop result has
  exactly the indices from result through size - 1. The two bounded universal
  clauses therefore preserve the source strict-prefix and
  greater-or-equal-suffix Boolean all tests, including empty ranges.

  The proof-valued precondition arguments to the implementation and
  postcondition have no computational or propositional effect beyond the
  explicit antecedent in the final correctness assertion. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB51ToList VERINAB51GetBang
  VERINAB51PairwiseLE VERINAB51Pre
  VERINAB51LoopGraph VERINAB51Loop
  VERINAB51BinarySearch VERINAB51Post
$.

verinab51-to-list-syntax
  $a class ( VERINAB51ToList A ) $.
verinab51-get-bang-syntax
  $a class ( VERINAB51GetBang A B ) $.
verinab51-pairwise-le-syntax
  $a wff ( VERINAB51PairwiseLE A ) $.
verinab51-precondition-syntax
  $a wff ( VERINAB51Pre A B ) $.
verinab51-loop-graph-syntax
  $a wff ( VERINAB51LoopGraph A B C D E ) $.
verinab51-loop-syntax
  $a class ( VERINAB51Loop A B C D ) $.
verinab51-program-syntax
  $a class ( VERINAB51BinarySearch A B ) $.
verinab51-postcondition-syntax
  $a wff ( VERINAB51Post A B C ) $.

verinab51-to-list-definition $a |- (
  VERINAB51ToList A
) = A $.

verinab51-get-bang-definition $a |- (
  VERINAB51GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i j A $.

  verinab51-pairwise-le-definition $a |- (
    VERINAB51PairwiseLE A
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

verinab51-precondition-definition $a |- (
  VERINAB51Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. ZZ
  )
  /\
  (
    VERINAB51PairwiseLE
      ( VERINAB51ToList A )
  )
) $.

${
  $d i l r A B C D E $.

  verinab51-loop-graph-definition $a |- (
    VERINAB51LoopGraph A B C D E
  ) <-> (
    (
      (
        (
          A e. Word ZZ
          /\
          B e. ZZ
        )
        /\
        (
          C e. NN0
          /\
          D e. NN0
        )
      )
      /\
      E e. NN0
    )
    /\
    E. l e. Word NN0
      E. r e. Word NN0
        (
          (
            (
              (
                ( # ` l ) = ( # ` r )
                /\
                0 < ( # ` l )
              )
              /\
              (
                ( l ` 0 ) = C
                /\
                ( r ` 0 ) = D
              )
            )
            /\
            (
              (
                r ` ( ( # ` r ) - 1 )
              ) <_ (
                l ` ( ( # ` l ) - 1 )
              )
              /\
              E = ( l ` ( ( # ` l ) - 1 ) )
            )
          )
          /\
          A. i e. ( 0 ..^ ( ( # ` l ) - 1 ) )
            (
              ( l ` i ) < ( r ` i )
              /\
              (
                (
                  l ` ( i + 1 )
                ) = if (
                  (
                    VERINAB51GetBang
                      A
                      (
                        |_ ` (
                          (
                            ( l ` i ) + ( r ` i )
                          ) / 2
                        )
                      )
                  ) < B ,
                  (
                    (
                      |_ ` (
                        (
                          ( l ` i ) + ( r ` i )
                        ) / 2
                      )
                    ) + 1
                  ) ,
                  ( l ` i )
                )
                /\
                (
                  r ` ( i + 1 )
                ) = if (
                  (
                    VERINAB51GetBang
                      A
                      (
                        |_ ` (
                          (
                            ( l ` i ) + ( r ` i )
                          ) / 2
                        )
                      )
                  ) < B ,
                  ( r ` i ) ,
                  (
                    |_ ` (
                      (
                        ( l ` i ) + ( r ` i )
                      ) / 2
                    )
                  )
                )
              )
            )
        )
  ) $.
$}

${
  $d y A B C D $.

  verinab51-loop-definition $a |- (
    VERINAB51Loop A B C D
  ) = (
    iota_ y e. NN0
      ( VERINAB51LoopGraph A B C D y )
  ) $.
$}

verinab51-program-definition $a |- (
  VERINAB51BinarySearch A B
) = (
  VERINAB51Loop A B 0 ( # ` A )
) $.

${
  $d i A B C $.

  verinab51-postcondition-definition $a |- (
    VERINAB51Post A B C
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
      C <_ ( # ` A )
      /\
      (
        A. i e. ( 0 ..^ C )
          ( A ` i ) < B
        /\
        A. i e. ( C ..^ ( # ` A ) )
          B <_ ( A ` i )
      )
    )
  ) $.
$}

verina-basic-51-binary-search
  $a |- A. w e. Word ZZ
    A. k e. ZZ
      (
        ( VERINAB51Pre w k )
        ->
        (
          VERINAB51Post
            w
            k
            ( VERINAB51BinarySearch w k )
        )
      )
  $.
