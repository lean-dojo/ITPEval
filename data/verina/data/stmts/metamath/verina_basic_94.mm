$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_94
  (verina__metamath__verina_basic_94), catalog title iter_copy: the exact
  executable left-to-right loop copies an arbitrary finite integer array by
  repeatedly appending its next entry to an initially empty array and
  satisfies the size-and-pointwise-equality contract. This file contains no
  proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` i is zero-based lookup,
  0 ..^ ( # ` w ) is its complete valid-index set, (/) is the empty word,
  <" x "> is a singleton word, and ++ is word concatenation.

  VERINAB94NatSub is Lean's truncated natural subtraction.
  VERINAB94GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array.

  VERINAB94LoopGraph is the exact complete execution trace of the source
  local loop for every integer array, natural starting index, and accumulator.
  Its trace has max(s.size - i, 0) transitions. Transition k appends the entry
  at index i + k to the current accumulator, exactly as Array.push does.
  Every such index is valid, so the source optional lookup is some of that
  entry; the source none branch is unreachable. If i is at or beyond the
  input size, the trace has no transition and returns the accumulator.
  VERINAB94Loop selects the unique final accumulator, and VERINAB94IterCopy
  invokes that exact loop at index zero with the empty array. Thus the
  executable result is fixed independently of the postcondition and admits
  no additional output.

  VERINAB94Pre is the source True precondition on typed Array Int inputs.
  VERINAB94Post preserves the source result-size equation and universal
  pointwise equality over all natural indices below the input size. The
  proof-valued precondition argument has no computational effect, and the
  postcondition does not inspect it, so the final correctness assertion
  represents it by the explicit precondition antecedent. Every earlier $a is
  syntax or a faithful definition required by this rendering, and this
  database has no $p declaration.
$)

$c
  VERINAB94NatSub VERINAB94GetBang
  VERINAB94LoopGraph VERINAB94Loop
  VERINAB94Pre VERINAB94IterCopy VERINAB94Post
$.

verinab94-nat-sub-syntax
  $a class ( VERINAB94NatSub A B ) $.
verinab94-get-bang-syntax
  $a class ( VERINAB94GetBang A B ) $.
verinab94-loop-graph-syntax
  $a wff ( VERINAB94LoopGraph A B C D ) $.
verinab94-loop-syntax
  $a class ( VERINAB94Loop A B C ) $.
verinab94-precondition-syntax
  $a wff ( VERINAB94Pre A ) $.
verinab94-program-syntax
  $a class ( VERINAB94IterCopy A ) $.
verinab94-postcondition-syntax
  $a wff ( VERINAB94Post A B ) $.

verinab94-nat-sub-definition $a |- (
  VERINAB94NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab94-get-bang-definition $a |- (
  VERINAB94GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d k t A B C D $.

  verinab94-loop-graph-definition $a |- (
    VERINAB94LoopGraph A B C D
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
      D e. Word ZZ
    )
    /\
    E. t e. Word ( Word ZZ )
      (
        (
          ( # ` t ) = (
            ( VERINAB94NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB94NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              ( t ` k )
              ++
              <" ( A ` ( B + k ) ) ">
            )
          /\
          D = (
            t ` ( VERINAB94NatSub ( # ` A ) B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab94-loop-definition $a |- (
    VERINAB94Loop A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB94LoopGraph A B C y )
  ) $.
$}

verinab94-precondition-definition $a |- (
  VERINAB94Pre A
) <-> (
  A e. Word ZZ
) $.

verinab94-program-definition $a |- (
  VERINAB94IterCopy A
) = (
  VERINAB94Loop A 0 (/)
) $.

${
  $d i A B $.

  verinab94-postcondition-definition $a |- (
    VERINAB94Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      ( # ` A ) = ( # ` B )
      /\
      A. i e. NN0
        (
          i < ( # ` A )
          ->
          (
            VERINAB94GetBang A i
          ) = (
            VERINAB94GetBang B i
          )
        )
    )
  ) $.
$}

verina-basic-94-iter-copy $a |- A. s e. Word ZZ
  (
    ( VERINAB94Pre s )
    ->
    (
      VERINAB94Post
        s
        ( VERINAB94IterCopy s )
    )
  )
$.
