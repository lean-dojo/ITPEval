$(
  Statement-only formalization of the VERINA corpus artifact
  verina_advanced_1, catalog title FindSingleNumber: an executable scan of a
  finite integer list returns the first value occurring exactly once, under
  the condition that every value occurs once or twice and exactly one list
  position contains a singleton value. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ is the full integer domain, and Word ZZ is exactly the type of
  arbitrary finite integer lists. For a word w, # ` w is its length, w ` k
  is zero-based lookup, and ran w is its membership set.

  VERINAFilterGraph x w v says that v is obtained from w by retaining exactly
  the entries equal to x in their original order. VERINAFilter is the unique
  such word. VERINACount is List.count, and VERINAMapCounts reproduces
  nums.map (fun x => nums.count x). VERINAPre therefore reproduces the source
  all/count precondition exactly.

  VERINAFindUnique original remaining is the exact closed-form graph of the
  source recursion: it returns the value at the least index of remaining
  whose multiplicity in original is one, and returns integer zero when no
  such index exists. Hence VERINAFindSingle w = VERINAFindUnique w w preserves
  the executable implementation on every input, not merely its postcondition.
  VERINAPost reproduces the nonempty, singleton-result, and universal
  double-occurrence clauses. The final $a assertion applies that executable
  result to the postcondition under the precondition; every earlier $a is
  syntax or a faithful definition, and this database has no $p declaration.
$)

$c
  VERINAFilterGraph VERINAFilter VERINACount VERINAMapCounts
  VERINAPre VERINAFindUnique VERINAFindSingle VERINAPost
$.

verina-filter-graph-syntax
  $a wff ( VERINAFilterGraph A B C ) $.
verina-filter-syntax
  $a class ( VERINAFilter A B ) $.
verina-count-syntax
  $a class ( VERINACount A B ) $.
verina-map-counts-syntax
  $a class ( VERINAMapCounts A ) $.
verina-pre-syntax
  $a wff ( VERINAPre A ) $.
verina-find-unique-syntax
  $a class ( VERINAFindUnique A B ) $.
verina-find-single-syntax
  $a class ( VERINAFindSingle A ) $.
verina-post-syntax
  $a wff ( VERINAPost A B ) $.

${
  $d i j k p A B C $.

  verina-filter-graph-definition $a |- (
    ( VERINAFilterGraph A B C )
    <->
    (
      (
        A e. ZZ
        /\
        B e. Word ZZ
      )
      /\
      (
        C e. Word ZZ
        /\
        E. p e. Word NN0
          (
            ( # ` p ) = ( # ` C )
            /\
            (
              A. i e. ( 0 ..^ ( # ` p ) )
                (
                  ( p ` i ) < ( # ` B )
                  /\
                  (
                    ( B ` ( p ` i ) ) = A
                    /\
                    ( C ` i ) = ( B ` ( p ` i ) )
                  )
                )
              /\
              (
                A. i e. ( 0 ..^ ( # ` p ) )
                  A. j e. ( 0 ..^ ( # ` p ) )
                    (
                      i < j
                      ->
                      ( p ` i ) < ( p ` j )
                    )
                /\
                A. k e. ( 0 ..^ ( # ` B ) )
                  (
                    ( B ` k ) = A
                    ->
                    E. i e. ( 0 ..^ ( # ` p ) )
                      ( p ` i ) = k
                  )
              )
            )
          )
      )
    )
  ) $.
$}

${
  $d C A B $.

  verina-filter-definition $a |- (
    VERINAFilter A B
  ) = (
    iota_ C e. Word ZZ
      ( VERINAFilterGraph A B C )
  ) $.
$}

${
  $d k A B $.

  verina-count-definition $a |- (
    VERINACount A B
  ) = (
    # ` {
      k e. ( 0 ..^ ( # ` B ) )
      |
      ( B ` k ) = A
    }
  ) $.
$}

${
  $d k A $.

  verina-map-counts-definition $a |- (
    VERINAMapCounts A
  ) = (
    k e. ( 0 ..^ ( # ` A ) )
    |->
    ( VERINACount ( A ` k ) A )
  ) $.
$}

${
  $d k A $.

  verina-precondition-definition $a |- (
    ( VERINAPre A )
    <->
    (
      A e. Word ZZ
      /\
      (
        A. k e. ( 0 ..^ ( # ` A ) )
          (
            ( VERINACount ( A ` k ) A ) = 1
            \/
            ( VERINACount ( A ` k ) A ) = 2
          )
        /\
        ( VERINACount 1 ( VERINAMapCounts A ) ) = 1
      )
    )
  ) $.
$}

${
  $d j k y A B $.

  verina-find-unique-definition $a |- (
    VERINAFindUnique A B
  ) = (
    iota_ y e. ZZ
      (
        E. k e. ( 0 ..^ ( # ` B ) )
          (
            ( VERINACount ( B ` k ) A ) = 1
            /\
            (
              y = ( B ` k )
              /\
              A. j e. ( 0 ..^ ( # ` B ) )
                (
                  j < k
                  ->
                  -. ( VERINACount ( B ` j ) A ) = 1
                )
            )
          )
        \/
        (
          -.
          E. k e. ( 0 ..^ ( # ` B ) )
            ( VERINACount ( B ` k ) A ) = 1
          /\
          y = 0
        )
      )
  ) $.
$}

verina-find-single-definition $a |- (
  VERINAFindSingle A
) = (
  VERINAFindUnique A A
) $.

${
  $d x A B $.

  verina-postcondition-definition $a |- (
    ( VERINAPost A B )
    <->
    (
      (
        A e. Word ZZ
        /\
        B e. ZZ
      )
      /\
      (
        0 < ( # ` A )
        /\
        (
          ( # ` ( VERINAFilter B A ) ) = 1
          /\
          A. x e. ZZ
            (
              x e. ran A
              ->
              (
                x = B
                \/
                ( # ` ( VERINAFilter x A ) ) = 2
              )
            )
        )
      )
    )
  ) $.
$}

verina-advanced-1-find-single-number $a |- A. w e. Word ZZ
  (
    ( VERINAPre w )
    ->
    ( VERINAPost w ( VERINAFindSingle w ) )
  )
$.
