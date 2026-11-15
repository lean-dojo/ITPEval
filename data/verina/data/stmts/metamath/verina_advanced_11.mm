$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_11, catalog title findMajorityElement: an executable
  left-to-right search of a finite integer list returns its first element
  occurring strictly more than half the list length, or integer -1 if no
  such element exists, together with its correctness contract. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and 0 ..^ ( # ` w ) is its complete index set.

  VERINA11Count x w is the cardinality of the indices of w containing x.
  This is exactly countOccurrences x w: the source foldl starts at zero and
  adds one precisely at those indices. VERINA11Half w is floor(length / 2),
  exactly Lean natural-number division by two. VERINA11Pre includes only the
  source list type because the Lean precondition is True.

  VERINA11FindGraph w y characterizes the executable find? exactly. Its first
  branch chooses the value at the least index whose occurrence count exceeds
  half the length; its second branch returns -1 exactly when no such index
  exists. VERINA11Find is the unique integer selected by this graph, so it
  preserves the source computation on every typed input rather than merely
  selecting an output satisfying the postcondition. The proof-valued
  precondition argument is computationally unused in Lean and is therefore
  omitted from the target function.

  VERINA11Majority and VERINA11Post reproduce the local count, n, majority,
  both result implications, and both list-wide all tests in the source
  postcondition. The final $a declaration is the source correctness
  proposition. Every earlier $a is syntax or a faithful definition, and this
  database has no $p declaration.
$)

$c
  VERINA11Count VERINA11Half VERINA11Pre VERINA11Heavy
  VERINA11Majority VERINA11FindGraph VERINA11Find VERINA11Post
$.

verina11-count-syntax
  $a class ( VERINA11Count A B ) $.
verina11-half-syntax
  $a class ( VERINA11Half A ) $.
verina11-precondition-syntax
  $a wff ( VERINA11Pre A ) $.
verina11-heavy-syntax
  $a wff ( VERINA11Heavy A B ) $.
verina11-majority-syntax
  $a wff ( VERINA11Majority A B ) $.
verina11-find-graph-syntax
  $a wff ( VERINA11FindGraph A B ) $.
verina11-find-syntax
  $a class ( VERINA11Find A ) $.
verina11-postcondition-syntax
  $a wff ( VERINA11Post A B ) $.

${
  $d k A B $.

  verina11-count-definition $a |- (
    VERINA11Count A B
  ) = (
    # ` {
      k e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` k ) = A
    }
  ) $.
$}

verina11-half-definition $a |- (
  VERINA11Half A
) = (
  |_ ` ( ( # ` A ) / 2 )
) $.

verina11-precondition-definition $a |- (
  ( VERINA11Pre A )
  <->
  A e. Word ZZ
) $.

verina11-heavy-definition $a |- (
  ( VERINA11Heavy A B )
  <->
  (
    (
      A e. Word ZZ
      /\
      B e. ZZ
    )
    /\
    ( VERINA11Half A ) < ( VERINA11Count B A )
  )
) $.

${
  $d k A B $.

  verina11-majority-definition $a |- (
    ( VERINA11Majority A B )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      (
        ( VERINA11Heavy A B )
        /\
        A. k e. ( 0 ..^ ( # ` A ) )
          (
            ( VERINA11Count ( A ` k ) A )
              <_ ( VERINA11Half A )
            \/
            ( A ` k ) = B
          )
      )
    )
  ) $.
$}

${
  $d j k A B $.

  verina11-find-graph-definition $a |- (
    ( VERINA11FindGraph A B )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      (
        E. k e. ( 0 ..^ ( # ` A ) )
          (
            ( VERINA11Heavy A ( A ` k ) )
            /\
            (
              B = ( A ` k )
              /\
              A. j e. ( 0 ..^ ( # ` A ) )
                (
                  j < k
                  ->
                  -. ( VERINA11Heavy A ( A ` j ) )
                )
            )
          )
        \/
        (
          -.
          E. k e. ( 0 ..^ ( # ` A ) )
            ( VERINA11Heavy A ( A ` k ) )
          /\
          B = ( -u 1 )
        )
      )
    )
  ) $.
$}

${
  $d y A $.

  verina11-find-definition $a |- (
    VERINA11Find A
  ) = (
    iota_ y e. ZZ
      ( VERINA11FindGraph A y )
  ) $.
$}

${
  $d k A B $.

  verina11-postcondition-definition $a |- (
    ( VERINA11Post A B )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      (
        (
          B = ( -u 1 )
          ->
          (
            A. k e. ( 0 ..^ ( # ` A ) )
              ( VERINA11Count ( A ` k ) A )
                <_ ( VERINA11Half A )
            \/
            ( VERINA11Majority A B )
          )
        )
        /\
        (
          B =/= ( -u 1 )
          ->
          ( VERINA11Majority A B )
        )
      )
    )
  ) $.
$}

verina-advanced-11-find-majority-element $a |- A. w e. Word ZZ
  (
    ( VERINA11Pre w )
    ->
    ( VERINA11Post w ( VERINA11Find w ) )
  )
$.
