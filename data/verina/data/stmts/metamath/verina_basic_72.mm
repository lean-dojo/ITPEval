$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_72
  (verina__metamath__verina_basic_72), catalog title append: the exact
  executable integer-array copy followed by a final push appends one integer
  and satisfies the pointwise, last-element, and size correctness contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  w, # ` w is its natural-number size, w ` i is zero-based lookup,
  0 ..^ n is the set of natural indices below n, and (/) is the empty word.

  VERINAB72NatSub is Lean's truncated natural subtraction.
  VERINAB72GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB72PushGraph and
  VERINAB72Push reproduce Array.push exactly.

  VERINAB72CopyGraph is the complete finite execution trace of the source
  recursive copy helper for every integer array A, natural starting index B,
  and accumulator C. It starts at C and performs exactly A.size - B
  truncated-at-zero transitions; transition k pushes get! A (B + k).
  Consequently it stops immediately when B is at or beyond A.size and
  otherwise follows precisely the source guard, recursive index increment,
  and accumulator push. VERINAB72Copy selects the unique final accumulator.

  VERINAB72Append is exactly the source executable program: copy the whole
  input from index zero into the empty array and then push b. VERINAB72Pre is
  the source True precondition on typed inputs. VERINAB72Post preserves the
  source List.range' all-condition over every original index, the get! value
  at the new last index, and the result-size equation. The proof-valued
  precondition arguments are computationally and propositionally unused and
  are represented by the explicit precondition antecedent in the final
  correctness assertion. Every earlier $a is syntax or a faithful definition
  required by this rendering, and this database has no $p declaration.
$)

$c
  VERINAB72NatSub VERINAB72GetBang
  VERINAB72PushGraph VERINAB72Push
  VERINAB72CopyGraph VERINAB72Copy
  VERINAB72Pre VERINAB72Append VERINAB72Post
$.

verinab72-nat-sub-syntax
  $a class ( VERINAB72NatSub A B ) $.
verinab72-get-bang-syntax
  $a class ( VERINAB72GetBang A B ) $.
verinab72-push-graph-syntax
  $a wff ( VERINAB72PushGraph A B C ) $.
verinab72-push-syntax
  $a class ( VERINAB72Push A B ) $.
verinab72-copy-graph-syntax
  $a wff ( VERINAB72CopyGraph A B C D ) $.
verinab72-copy-syntax
  $a class ( VERINAB72Copy A B C ) $.
verinab72-precondition-syntax
  $a wff ( VERINAB72Pre A B ) $.
verinab72-program-syntax
  $a class ( VERINAB72Append A B ) $.
verinab72-postcondition-syntax
  $a wff ( VERINAB72Post A B C ) $.

verinab72-nat-sub-definition $a |- (
  VERINAB72NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab72-get-bang-definition $a |- (
  VERINAB72GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

${
  $d i A B C $.

  verinab72-push-graph-definition $a |- (
    VERINAB72PushGraph A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      ( # ` C ) = ( ( # ` A ) + 1 )
      /\
      (
        A. i e. ( 0 ..^ ( # ` A ) )
          ( C ` i ) = ( A ` i )
        /\
        ( C ` ( # ` A ) ) = B
      )
    )
  ) $.
$}

${
  $d y A B $.

  verinab72-push-definition $a |- (
    VERINAB72Push A B
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB72PushGraph A B y )
  ) $.
$}

${
  $d k t A B C D $.

  verinab72-copy-graph-definition $a |- (
    VERINAB72CopyGraph A B C D
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
            ( VERINAB72NatSub ( # ` A ) B ) + 1
          )
          /\
          ( t ` 0 ) = C
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB72NatSub ( # ` A ) B )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB72Push
                ( t ` k )
                (
                  VERINAB72GetBang A ( B + k )
                )
            )
          /\
          D = (
            t ` ( VERINAB72NatSub ( # ` A ) B )
          )
        )
      )
  ) $.
$}

${
  $d y A B C $.

  verinab72-copy-definition $a |- (
    VERINAB72Copy A B C
  ) = (
    iota_ y e. Word ZZ
      ( VERINAB72CopyGraph A B C y )
  ) $.
$}

verinab72-precondition-definition $a |- (
  VERINAB72Pre A B
) <-> (
  A e. Word ZZ
  /\
  B e. ZZ
) $.

verinab72-program-definition $a |- (
  VERINAB72Append A B
) = (
  VERINAB72Push
    ( VERINAB72Copy A 0 (/) )
    B
) $.

${
  $d i A B C $.

  verinab72-postcondition-definition $a |- (
    VERINAB72Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      C e. Word ZZ
    )
    /\
    (
      A. i e. ( 0 ..^ ( # ` A ) )
        (
          VERINAB72GetBang C i
        ) = (
          VERINAB72GetBang A i
        )
      /\
      (
        (
          VERINAB72GetBang C ( # ` A )
        ) = B
        /\
        ( # ` C ) = ( ( # ` A ) + 1 )
      )
    )
  ) $.
$}

verina-basic-72-append $a |- A. a e. Word ZZ
  A. b e. ZZ
    (
      ( VERINAB72Pre a b )
      ->
      (
        VERINAB72Post
          a
          b
          ( VERINAB72Append a b )
      )
    )
$.
