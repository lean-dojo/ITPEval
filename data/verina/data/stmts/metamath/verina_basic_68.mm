$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_68
  (verina__metamath__verina_basic_68), catalog title LinearSearch: the exact
  executable left-to-right scan of an arbitrary finite integer array returns
  the first matching index, or the array size when absent, and satisfies its
  full correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` i is zero-based lookup, and
  0 ..^ n is the set of natural indices below n.

  VERINAB68GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array.

  VERINAB68LoopGraph is the exact graph of the source local recursive loop
  for every typed array, integer target, and natural starting index. A start
  at or beyond the array size returns that start unchanged. Otherwise its
  witness p counts the consecutive unequal in-bounds entries skipped by the
  recursive n + 1 branch. The terminal index is either the first matching
  entry or exactly the array size, and the result is that terminal index.
  Consequently the graph admits precisely the source loop's result, with no
  additional outputs. VERINAB68Loop selects this unique result.

  VERINAB68Pre is the source True precondition together with the input types.
  VERINAB68LinearSearch is exactly the executable source call loop 0.
  VERINAB68Post preserves the source postcondition: the result is at most the
  array size, is either the size or indexes the target, and every earlier
  index contains a different integer. The proof-valued precondition arguments
  to the implementation and postcondition are computationally and
  propositionally unused beyond the explicit precondition antecedent in the
  final correctness assertion. Every earlier $a is syntax or a faithful
  definition required by this rendering, and this database has no $p
  declaration.
$)

$c
  VERINAB68GetBang VERINAB68LoopGraph VERINAB68Loop
  VERINAB68Pre VERINAB68LinearSearch VERINAB68Post
$.

verinab68-get-bang-syntax
  $a class ( VERINAB68GetBang A B ) $.
verinab68-loop-graph-syntax
  $a wff ( VERINAB68LoopGraph A B C D ) $.
verinab68-loop-syntax
  $a class ( VERINAB68Loop A B C ) $.
verinab68-precondition-syntax
  $a wff ( VERINAB68Pre A B ) $.
verinab68-program-syntax
  $a class ( VERINAB68LinearSearch A B ) $.
verinab68-postcondition-syntax
  $a wff ( VERINAB68Post A B C ) $.

verinab68-get-bang-definition $a |- (
  VERINAB68GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k p A B C D $.

  verinab68-loop-graph-definition $a |- (
    VERINAB68LoopGraph A B C D
  ) <-> (
    (
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
      D e. NN0
    )
    /\
    (
      (
        ( # ` A ) <_ C
        /\
        D = C
      )
      \/
      (
        C < ( # ` A )
        /\
        E. p e. NN0
          (
            (
              (
                ( C + p ) <_ ( # ` A )
                /\
                A. k e. ( 0 ..^ p )
                  ( A ` ( C + k ) ) =/= B
              )
              /\
              (
                (
                  ( C + p ) < ( # ` A )
                  /\
                  ( A ` ( C + p ) ) = B
                )
                \/
                ( C + p ) = ( # ` A )
              )
            )
            /\
            D = ( C + p )
          )
      )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab68-loop-definition $a |- (
    VERINAB68Loop A B C
  ) = (
    iota_ y e. NN0
      ( VERINAB68LoopGraph A B C y )
  ) $.
$}

verinab68-precondition-definition $a |- (
  VERINAB68Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

verinab68-program-definition $a |- (
  VERINAB68LinearSearch A B
) = (
  VERINAB68Loop A B 0
) $.

${
  $d i A B C $.

  verinab68-postcondition-definition $a |- (
    VERINAB68Post A B C
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
        (
          C = ( # ` A )
          \/
          ( VERINAB68GetBang A C ) = B
        )
        /\
        A. i e. NN0
          (
            i < C
            ->
            ( VERINAB68GetBang A i ) =/= B
          )
      )
    )
  ) $.
$}

verina-basic-68-linear-search $a |- A. w e. Word ZZ
  A. e e. ZZ
    (
      ( VERINAB68Pre w e )
      ->
      (
        VERINAB68Post
          w
          e
          ( VERINAB68LinearSearch w e )
      )
    )
$.
