$(
  Statement-only formalization of the VERINA corpus artifact verina_basic_79
  (verina__metamath__verina_basic_79), catalog title onlineMax: the exact
  recursive prefix-maximum and first-later-exceeding-index program on a
  nonempty finite integer array satisfies its complete ordering contract.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  SetMM's ZZ and NN0 are the full integer and natural-number domains, and
  Word ZZ is exactly the type of arbitrary finite integer arrays. For a word
  a, # ` a is its natural-number size, a ` i is zero-based lookup, and
  0 ..^ n is the set of natural indices below n.

  VERINAB79GetBang reproduces Lean Array.get! on integer arrays, including
  its inhabited default value zero outside the array. VERINAB79NatSub is
  Lean's truncated natural subtraction. VERINAB79MaxStep reproduces the
  strict source conditional: it takes the new array value exactly when that
  value is greater than the current best, and otherwise retains the best.

  VERINAB79FindBestGraph is the complete finite execution trace of findBest
  for every typed array, bound x, starting index i, and integer accumulator.
  The trace has max(x - i, 0) transitions. Transition k reads a[i + k]!,
  applies the exact maximum update, and the graph returns the final
  accumulator. VERINAB79FindBest selects this unique result.

  VERINAB79FindPGraph is the exact deterministic graph of findP for every
  typed helper argument. Its witness p is the number of consecutive entries
  at or below m beginning at i, bounded by a.size - i. If p is smaller than
  that bound, a[i + p]! is strictly greater than m and the result is i + p.
  If p equals the bound, the scan is exhausted and the result is a.size - 1
  with truncated natural subtraction. The helper's x argument is retained
  with its Nat type and is intentionally unused, exactly as in the source.
  VERINAB79FindP selects the unique graph result.

  VERINAB79Pre preserves a.size > 0, x > 0, and x < a.size.
  VERINAB79OnlineMax first invokes findBest a x 1 a[0]!, then invokes findP
  a x on that exact maximum starting at x, and returns the ordered pair.
  VERINAB79Post preserves every source conjunct: the result index bounds,
  prefix upper bound and attained maximum, the upper bound before p, and
  either a strict exceedance at p or the last-index fallback with no later
  exceedance. The proof-valued precondition arguments to the implementation
  and postcondition are computationally and propositionally unused beyond
  the explicit precondition antecedent in the final correctness assertion.
  Every earlier $a is syntax or a faithful definition required by this
  rendering, and this database has no $p declaration.
$)

$c
  VERINAB79GetBang VERINAB79NatSub VERINAB79MaxStep
  VERINAB79FindBestGraph VERINAB79FindBest
  VERINAB79FindPGraph VERINAB79FindP
  VERINAB79Pre VERINAB79OnlineMax VERINAB79Post
$.

verinab79-get-bang-syntax
  $a class ( VERINAB79GetBang A B ) $.
verinab79-nat-sub-syntax
  $a class ( VERINAB79NatSub A B ) $.
verinab79-max-step-syntax
  $a class ( VERINAB79MaxStep A B ) $.
verinab79-find-best-graph-syntax
  $a wff ( VERINAB79FindBestGraph A B C D E ) $.
verinab79-find-best-syntax
  $a class ( VERINAB79FindBest A B C D ) $.
verinab79-find-p-graph-syntax
  $a wff ( VERINAB79FindPGraph A B C D E ) $.
verinab79-find-p-syntax
  $a class ( VERINAB79FindP A B C D ) $.
verinab79-precondition-syntax
  $a wff ( VERINAB79Pre A B ) $.
verinab79-program-syntax
  $a class ( VERINAB79OnlineMax A B ) $.
verinab79-postcondition-syntax
  $a wff ( VERINAB79Post A B C ) $.

verinab79-get-bang-definition $a |- (
  VERINAB79GetBang A B
) = if (
  B < ( # ` A ) ,
  ( A ` B ) ,
  0
) $.

verinab79-nat-sub-definition $a |- (
  VERINAB79NatSub A B
) = if (
  A < B ,
  0 ,
  ( A - B )
) $.

verinab79-max-step-definition $a |- (
  VERINAB79MaxStep A B
) = if (
  B < A ,
  A ,
  B
) $.

${
  $d k t A B C D E $.

  verinab79-find-best-graph-definition $a |- (
    VERINAB79FindBestGraph A B C D E
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
          C e. NN0
        )
        /\
        D e. ZZ
      )
      /\
      E e. ZZ
    )
    /\
    E. t e. Word ZZ
      (
        (
          ( # ` t ) = (
            ( VERINAB79NatSub B C ) + 1
          )
          /\
          ( t ` 0 ) = D
        )
        /\
        (
          A. k e. (
            0 ..^ ( VERINAB79NatSub B C )
          )
            (
              t ` ( k + 1 )
            ) = (
              VERINAB79MaxStep
                ( VERINAB79GetBang A ( C + k ) )
                ( t ` k )
            )
          /\
          E = (
            t ` ( VERINAB79NatSub B C )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab79-find-best-definition $a |- (
    VERINAB79FindBest A B C D
  ) = (
    iota_ y e. ZZ
      ( VERINAB79FindBestGraph A B C D y )
  ) $.
$}

${
  $d j p A B C D E $.

  verinab79-find-p-graph-definition $a |- (
    VERINAB79FindPGraph A B C D E
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
          C e. ZZ
        )
        /\
        D e. NN0
      )
      /\
      E e. NN0
    )
    /\
    E. p e. NN0
      (
        p <_ (
          VERINAB79NatSub
            ( # ` A )
            D
        )
        /\
        (
          A. j e. ( 0 ..^ p )
            (
              VERINAB79GetBang
                A
                ( D + j )
            ) <_ C
          /\
          (
            (
              p < (
                VERINAB79NatSub
                  ( # ` A )
                  D
              )
              /\
              (
                C < (
                  VERINAB79GetBang
                    A
                    ( D + p )
                )
                /\
                E = ( D + p )
              )
            )
            \/
            (
              p = (
                VERINAB79NatSub
                  ( # ` A )
                  D
              )
              /\
              E = (
                VERINAB79NatSub
                  ( # ` A )
                  1
              )
            )
          )
        )
      )
  ) $.
$}

${
  $d y A B C D $.

  verinab79-find-p-definition $a |- (
    VERINAB79FindP A B C D
  ) = (
    iota_ y e. NN0
      ( VERINAB79FindPGraph A B C D y )
  ) $.
$}

verinab79-precondition-definition $a |- (
  VERINAB79Pre A B
) <-> (
  (
    A e. Word ZZ
    /\
    B e. NN0
  )
  /\
  (
    0 < ( # ` A )
    /\
    (
      0 < B
      /\
      B < ( # ` A )
    )
  )
) $.

verinab79-program-definition $a |- (
  VERINAB79OnlineMax A B
) = <.
  (
    VERINAB79FindBest
      A
      B
      1
      ( VERINAB79GetBang A 0 )
  )
  ,
  (
    VERINAB79FindP
      A
      B
      (
        VERINAB79FindBest
          A
          B
          1
          ( VERINAB79GetBang A 0 )
      )
      B
  )
>. $.

${
  $d i A B C $.

  verinab79-postcondition-definition $a |- (
    VERINAB79Post A B C
  ) <-> (
    (
      (
        A e. Word ZZ
        /\
        B e. NN0
      )
      /\
      C e. ( ZZ X. NN0 )
    )
    /\
    (
      (
        B <_ ( 2nd ` C )
        /\
        ( 2nd ` C ) < ( # ` A )
      )
      /\
      (
        A. i e. NN0
          (
            i < B
            ->
            (
              VERINAB79GetBang A i
            ) <_ ( 1st ` C )
          )
        /\
        (
          E. i e. NN0
            (
              i < B
              /\
              (
                VERINAB79GetBang A i
              ) = ( 1st ` C )
            )
          /\
          (
            A. i e. NN0
              (
                B <_ i
                ->
                (
                  i < ( 2nd ` C )
                  ->
                  (
                    VERINAB79GetBang A i
                  ) <_ ( 1st ` C )
                )
              )
            /\
            (
              (
                ( 1st ` C ) < (
                  VERINAB79GetBang
                    A
                    ( 2nd ` C )
                )
              )
              \/
              (
                (
                  2nd ` C
                ) = (
                  VERINAB79NatSub
                    ( # ` A )
                    1
                )
                /\
                A. i e. NN0
                  (
                    B <_ i
                    ->
                    (
                      i < ( # ` A )
                      ->
                      (
                        VERINAB79GetBang A i
                      ) <_ ( 1st ` C )
                    )
                  )
              )
            )
          )
        )
      )
    )
  ) $.
$}

verina-basic-79-online-max $a |- A. a e. Word ZZ
  A. x e. NN0
    (
      ( VERINAB79Pre a x )
      ->
      (
        VERINAB79Post
          a
          x
          ( VERINAB79OnlineMax a x )
      )
    )
$.
