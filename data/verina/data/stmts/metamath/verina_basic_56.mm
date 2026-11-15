$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_56
  (verina__metamath__verina_basic_56), catalog title copy: the exact
  executable descending-index segment copy replaces the designated part of a
  finite integer destination array from a finite integer source array and
  satisfies its size, preservation, and copied-entry contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number length, w ` i is zero-based lookup, and
  0 ..^ n is the set of natural indices below n.

  VERINAB56NatSub is Lean's truncated natural subtraction.
  VERINAB56GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB56SetBangGraph
  and its iota-selected function reproduce Array.set!, including unchanged
  array behavior at an out-of-range index.

  VERINAB56UpdateSegmentGraph is the exact finite execution trace of the
  source recursive updateSegment helper. For length n, transition k writes
  offset n - 1 - k, so the writes occur in the source order n - 1 down to
  zero. Each transition reads the immutable source array with get! and
  applies set! to the current destination state. VERINAB56UpdateSegment
  selects the unique final array fixed by that trace.

  VERINAB56Pre preserves both source bounds assumptions.
  VERINAB56Copy preserves the explicit zero-length branch and otherwise calls
  updateSegment on the original destination. VERINAB56Post preserves the
  result-size equation, the unchanged prefix and suffix conditions, and the
  copied-segment equation. The proof-valued precondition arguments to the
  implementation and postcondition are computationally and propositionally
  unused beyond the explicit precondition antecedent in the final correctness
  assertion. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINAB56NatSub VERINAB56GetBang
  VERINAB56SetBangGraph VERINAB56SetBang
  VERINAB56UpdateSegmentGraph VERINAB56UpdateSegment
  VERINAB56Pre VERINAB56Copy VERINAB56Post
$.

verinab56-nat-sub-syntax
  $a class ( VERINAB56NatSub A B ) $.
verinab56-get-bang-syntax
  $a class ( VERINAB56GetBang A B ) $.
verinab56-set-bang-graph-syntax
  $a wff ( VERINAB56SetBangGraph A B C D ) $.
verinab56-set-bang-syntax
  $a class ( VERINAB56SetBang A B C ) $.
verinab56-update-segment-graph-syntax
  $a wff ( VERINAB56UpdateSegmentGraph A B C D E F ) $.
verinab56-update-segment-syntax
  $a class ( VERINAB56UpdateSegment A B C D E ) $.
verinab56-precondition-syntax
  $a wff ( VERINAB56Pre A B C D E ) $.
verinab56-program-syntax
  $a class ( VERINAB56Copy A B C D E ) $.
verinab56-postcondition-syntax
  $a wff ( VERINAB56Post A B C D E F ) $.

verinab56-nat-sub-definition $a |- (
  VERINAB56NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab56-get-bang-definition $a |- (
  VERINAB56GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C D $.

  verinab56-set-bang-graph-definition $a |- (
    VERINAB56SetBangGraph A B C D
  ) <-> (
    (
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
      D e. Word ZZ
    )
    /\
    (
      ( # ` D ) = ( # ` A )
      /\
      A. i e. ( 0 ..^ ( # ` A ) )
        ( D ` i ) = if (
          i = B ,
          C ,
          ( A ` i )
        )
    )
  ) $.
$}

${
  $d y A B C $.

  verinab56-set-bang-definition $a |- (
    VERINAB56SetBang A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB56SetBangGraph A B C y )
  ) $.
$}

${
  $d k t A B C D E F $.

  verinab56-update-segment-graph-definition $a |- (
    VERINAB56UpdateSegmentGraph A B C D E F
  ) <-> (
    (
      (
        (
          (
            A e. Word ZZ
            /\
            B e. Word ZZ
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
      F e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = ( E + 1 )
          /\
          ( t ` 0 ) = A
        )
        /\
        (
          A. k e. ( 0 ..^ E )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB56SetBang
                ( t ` k )
                (
                  D
                  +
                  (
                    VERINAB56NatSub
                      ( VERINAB56NatSub E 1 )
                      k
                  )
                )
                (
                  VERINAB56GetBang
                    B
                    (
                      C
                      +
                      (
                        VERINAB56NatSub
                          ( VERINAB56NatSub E 1 )
                          k
                      )
                    )
                )
            )
          /\
          F = ( t ` E )
        )
      )
  ) $.
$}

${
  $d y A B C D E $.

  verinab56-update-segment-definition $a |- (
    VERINAB56UpdateSegment A B C D E
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB56UpdateSegmentGraph A B C D E y )
  ) $.
$}

verinab56-precondition-definition $a |- (
  VERINAB56Pre A B C D E
) <-> (
  (
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
      D e. NN0
      /\
      E e. NN0
    )
  )
  /\
  (
    ( B + E ) <_ ( # ` A )
    /\
    ( D + E ) <_ ( # ` C )
  )
) $.

verinab56-program-definition $a |- (
  VERINAB56Copy A B C D E
) = if (
  E = 0 ,
  C ,
  ( VERINAB56UpdateSegment C A B D E )
) $.

${
  $d i A B C D E F $.

  verinab56-postcondition-definition $a |- (
    VERINAB56Post A B C D E F
  ) <-> (
    (
      (
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
          D e. NN0
          /\
          E e. NN0
        )
      )
      /\
      F e. Word ZZ
    )
    /\
    (
      ( # ` F ) = ( # ` C )
      /\
      (
        A. i e. NN0
          (
            i < D
            ->
            (
              VERINAB56GetBang F i
            ) = (
              VERINAB56GetBang C i
            )
          )
        /\
        (
          A. i e. NN0
            (
              ( D + E ) <_ i
              ->
              (
                i < ( # ` F )
                ->
                (
                  VERINAB56GetBang F i
                ) = (
                  VERINAB56GetBang C i
                )
              )
            )
          /\
          A. i e. NN0
            (
              i < E
              ->
              (
                VERINAB56GetBang F ( D + i )
              ) = (
                VERINAB56GetBang A ( B + i )
              )
            )
        )
      )
    )
  ) $.
$}

verina-basic-56-copy $a |- A. u e. Word ZZ
  A. s e. NN0
    A. v e. Word ZZ
      A. d e. NN0
        A. n e. NN0
          (
            ( VERINAB56Pre u s v d n )
            ->
            (
              VERINAB56Post
                u
                s
                v
                d
                n
                ( VERINAB56Copy u s v d n )
            )
          )
$.
