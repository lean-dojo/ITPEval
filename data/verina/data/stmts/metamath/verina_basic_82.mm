$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_82
  (verina__metamath__verina_basic_82), catalog title remove_front: the exact
  recursive integer-array program copies all entries after the first into a
  fresh array and satisfies the nonempty-input, output-size, and pointwise
  shift correctness contract. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` k is zero-based lookup, (/) is the
  empty word, <" x "> is a singleton word, ++ is word concatenation, and
  0 ..^ n is the complete set of natural indices below n.

  VERINAB82NatSub is Lean's truncated natural subtraction. VERINAB82GetBang
  is Array.get! on Array Int, including the inhabited default value zero
  outside the array. VERINAB82MkEmpty preserves Array.mkEmpty: its natural
  argument is a capacity hint, while its Array value is the empty word.

  VERINAB82CopyFromGraph is the exact finite execution trace of the recursive
  source helper copyFrom for every typed array, natural starting index, and
  accumulator. It has max(a.size - i, 0) transitions. At transition k it
  appends exactly a[i + k]! to the current accumulator, reproducing
  Array.push; its final trace entry is the result. VERINAB82CopyFrom selects
  that unique final accumulator, so it permits no outputs beyond the source
  computation.

  VERINAB82RemoveFront retains the source size test, starts copyFrom at one,
  and passes Array.mkEmpty (a.size - 1). The false branch is Lean panic's
  inhabited default Array Int value, the empty array; under VERINAB82Pre this
  branch is unreachable. VERINAB82Post preserves the source nonemptiness
  conjunct, truncated output-size equation, and universally quantified
  get!-shift equation with its original natural-number bound.

  The proof-valued precondition argument is represented by the explicit
  antecedent of the final correctness assertion and has no other runtime
  content. Every earlier $a is syntax or a faithful definition required by
  this rendering, and this database has no $p declaration.
$)

$c
  VERINAB82NatSub VERINAB82GetBang VERINAB82MkEmpty
  VERINAB82CopyFromGraph VERINAB82CopyFrom
  VERINAB82Pre VERINAB82RemoveFront VERINAB82Post
$.

verinab82-nat-sub-syntax
  $a class ( VERINAB82NatSub A B ) $.
verinab82-get-bang-syntax
  $a class ( VERINAB82GetBang A B ) $.
verinab82-mk-empty-syntax
  $a class ( VERINAB82MkEmpty A ) $.
verinab82-copy-from-graph-syntax
  $a wff ( VERINAB82CopyFromGraph A B C D ) $.
verinab82-copy-from-syntax
  $a class ( VERINAB82CopyFrom A B C ) $.
verinab82-precondition-syntax
  $a wff ( VERINAB82Pre A ) $.
verinab82-program-syntax
  $a class ( VERINAB82RemoveFront A ) $.
verinab82-postcondition-syntax
  $a wff ( VERINAB82Post A B ) $.

verinab82-nat-sub-definition $a |- (
  VERINAB82NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab82-get-bang-definition $a |- (
  VERINAB82GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab82-mk-empty-definition $a |- (
  VERINAB82MkEmpty A
) = (/) $.

${
  $d k t A B C D $.

  verinab82-copy-from-graph-definition $a |- (
    VERINAB82CopyFromGraph A B C D
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
            ( VERINAB82NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB82NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              ( t ` k )
              ++
              <" ( VERINAB82GetBang A ( B + k ) ) ">
            )
          /\
          D = (
            t ` ( VERINAB82NatSub ( # ` A ) B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab82-copy-from-definition $a |- (
    VERINAB82CopyFrom A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB82CopyFromGraph A B C y )
  ) $.
$}

verinab82-precondition-definition $a |- (
  VERINAB82Pre A
) <-> (
  A e. Word ZZ
  /\
  0 < ( # ` A )
) $.

verinab82-program-definition $a |- (
  VERINAB82RemoveFront A
) = if (
  0 < ( # ` A ) ,
  (
    VERINAB82CopyFrom
      A
      1
      (
        VERINAB82MkEmpty
          ( VERINAB82NatSub ( # ` A ) 1 )
      )
  ) ,
  (/)
) $.

${
  $d k A B $.

  verinab82-postcondition-definition $a |- (
    VERINAB82Post A B
  ) <-> (
    (
      A e. Word ZZ
      /\
      B e. Word ZZ
    )
    /\
    (
      0 < ( # ` A )
      /\
      (
        ( # ` B ) = (
          VERINAB82NatSub ( # ` A ) 1
        )
        /\
        A. k e. NN0
          (
            k < ( # ` B )
            ->
            (
              VERINAB82GetBang B k
            ) = (
              VERINAB82GetBang A ( k + 1 )
            )
          )
      )
    )
  ) $.
$}

verina-basic-82-remove-front $a |- A. a e. Word ZZ
  (
    ( VERINAB82Pre a )
    ->
    (
      VERINAB82Post
        a
        ( VERINAB82RemoveFront a )
    )
  )
$.
