$(
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/warshall_algorithm_WarshallAlgorithm_transitive_closureqtvc: the
  Warshall Boolean-matrix transitive-closure verification condition, including
  its bounded-path relation and all three nested loop invariants. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  NTP4VCMatrix is the full source matrix type: two nonnegative integer
  dimensions together with an arbitrary total Boolean-valued function on all
  integer index pairs. Booleans use the exact two-element carrier { 0, 1 },
  with 0 false and 1 true.

  NTP4VCPath is bidirectionally equivalent to the source inductive path
  relation. Its witness is a finite integer sequence with at least one edge:
  each adjacent pair is an edge of the original Boolean matrix, and every
  internal vertex lies in the half-open integer interval [0,k). A direct edge
  gives Path_empty. Concatenating witnesses at an admissible internal vertex
  gives Path_cons; conversely, induction on sequence length gives a constructor
  derivation.

  NTP4VCInvariant, NTP4VCRowInvariant, and NTP4VCColumnInvariant are the
  generated k-, i-, and j-loop invariants. The remaining biconditional
  definitions factor the complete nested verification condition without
  changing its quantifier scopes. NTP4VCMatrixUpdate is the uncurried,
  full-integer-domain form of the nested Function.update equality. Source
  let-bindings are substituted definitionally, and proposition-valued
  conditionals are rendered as equivalent exhaustive guarded implications.

  Expanding these definitions recovers every source matrix and integer
  quantifier, all four initial assumptions, every loop-range branch, every
  intermediate same-shaped matrix, the Boolean update value, and the final
  transitive-closure invariant. Every $a before the final declaration is
  syntax or a faithful definition. The final $a is Metamath's native unproved
  statement encoding; this database contains no $p declaration.
$)

$c
  NTP4VCMatrix NTP4VCRows NTP4VCColumns NTP4VCElts NTP4VCEntry
  NTP4VCSameShape NTP4VCValidIndex NTP4VCCopy NTP4VCMatrixUpdate
  NTP4VCPath NTP4VCInvariant NTP4VCRowInvariant NTP4VCColumnInvariant
  NTP4VCNextValue NTP4VCCell NTP4VCColumnLoop NTP4VCRowLoop
  NTP4VCOuterLoop
$.

ntp4vc-matrix-syntax $a class NTP4VCMatrix $.
ntp4vc-rows-syntax $a class ( NTP4VCRows A ) $.
ntp4vc-columns-syntax $a class ( NTP4VCColumns A ) $.
ntp4vc-elts-syntax $a class ( NTP4VCElts A ) $.
ntp4vc-entry-syntax $a class ( NTP4VCEntry A B C ) $.

ntp4vc-same-shape-syntax
  $a wff ( NTP4VCSameShape A B ) $.
ntp4vc-valid-index-syntax
  $a wff ( NTP4VCValidIndex A B C ) $.
ntp4vc-copy-syntax
  $a wff ( NTP4VCCopy A B ) $.
ntp4vc-matrix-update-syntax
  $a wff ( NTP4VCMatrixUpdate A B C D E ) $.
ntp4vc-path-syntax
  $a wff ( NTP4VCPath A B C D ) $.
ntp4vc-invariant-syntax
  $a wff ( NTP4VCInvariant A B C D ) $.
ntp4vc-row-invariant-syntax
  $a wff ( NTP4VCRowInvariant A B C D E ) $.
ntp4vc-column-invariant-syntax
  $a wff ( NTP4VCColumnInvariant A B C D E F ) $.
ntp4vc-next-value-syntax
  $a wff ( NTP4VCNextValue A B C D E ) $.
ntp4vc-cell-syntax
  $a wff ( NTP4VCCell A B C D E F ) $.
ntp4vc-column-loop-syntax
  $a wff ( NTP4VCColumnLoop A B C D E ) $.
ntp4vc-row-loop-syntax
  $a wff ( NTP4VCRowLoop A B C D ) $.
ntp4vc-outer-loop-syntax
  $a wff ( NTP4VCOuterLoop A B C ) $.

ntp4vc-matrix-definition $a |- NTP4VCMatrix =
  (
    ( NN0 X. NN0 )
    X.
    ( { 0 , 1 } ^m ( ZZ X. ZZ ) )
  )
$.

ntp4vc-rows-definition $a |- (
  NTP4VCRows A
) = (
  1st ` ( 1st ` A )
) $.

ntp4vc-columns-definition $a |- (
  NTP4VCColumns A
) = (
  2nd ` ( 1st ` A )
) $.

ntp4vc-elts-definition $a |- (
  NTP4VCElts A
) = (
  2nd ` A
) $.

ntp4vc-entry-definition $a |- (
  NTP4VCEntry A B C
) = (
  ( NTP4VCElts A ) ` <. B , C >.
) $.

ntp4vc-same-shape-definition $a |- (
  NTP4VCSameShape A B
) <->
(
  ( NTP4VCRows A ) = ( NTP4VCRows B )
  /\
  ( NTP4VCColumns A ) = ( NTP4VCColumns B )
) $.

ntp4vc-valid-index-definition $a |- (
  NTP4VCValidIndex A B C
) <->
(
  (
    0 <_ B
    /\
    B < ( NTP4VCRows A )
  )
  /\
  (
    0 <_ C
    /\
    C < ( NTP4VCColumns A )
  )
) $.

${
  $d c r A B $.

  ntp4vc-copy-definition $a |- (
    NTP4VCCopy A B
  ) <->
  A. r e. ZZ
    (
      (
        0 <_ r
        /\
        r < ( NTP4VCRows A )
      )
      ->
      A. c e. ZZ
        (
          (
            0 <_ c
            /\
            c < ( NTP4VCColumns A )
          )
          ->
          (
            ( NTP4VCEntry A r c )
            =
            ( NTP4VCEntry B r c )
          )
        )
    ) $.
$}

${
  $d q A B C D E $.

  ntp4vc-matrix-update-definition $a |- (
    NTP4VCMatrixUpdate A B C D E
  ) <->
  (
    NTP4VCElts A
  )
  =
  (
    q e. ( ZZ X. ZZ ) |->
      if (
        ( 1st ` q ) = C ,
        if (
          ( 2nd ` q ) = D ,
          E ,
          (
            NTP4VCEntry
              B
              ( 1st ` q )
              ( 2nd ` q )
          )
        ) ,
        (
          NTP4VCEntry
            B
            ( 1st ` q )
            ( 2nd ` q )
        )
      )
  ) $.
$}

${
  $d l q A B C D $.

  ntp4vc-path-definition $a |- (
    NTP4VCPath A B C D
  ) <->
  E. l e. Word ZZ
    (
      2 <_ ( # ` l )
      /\
      (
        ( l ` 0 ) = B
        /\
        (
          ( l ` ( ( # ` l ) - 1 ) ) = C
          /\
          (
            A. q e. ( 0 ..^ ( ( # ` l ) - 1 ) )
              (
                NTP4VCEntry
                  A
                  ( l ` q )
                  ( l ` ( q + 1 ) )
              )
              =
              1
            /\
            A. q e. ( 1 ..^ ( ( # ` l ) - 1 ) )
              (
                0 <_ ( l ` q )
                /\
                ( l ` q ) < D
              )
          )
        )
      )
    ) $.
$}

${
  $d x y A B C D $.

  ntp4vc-invariant-definition $a |- (
    NTP4VCInvariant A B C D
  ) <->
  A. x e. ZZ
    A. y e. ZZ
      (
        (
          0 <_ x
          /\
          x < C
        )
        ->
        (
          (
            0 <_ y
            /\
            y < C
          )
          ->
          (
            (
              NTP4VCEntry B x y
            )
            =
            1
            <->
            ( NTP4VCPath A x y D )
          )
        )
      ) $.
$}

${
  $d x y A B C D E $.

  ntp4vc-row-invariant-definition $a |- (
    NTP4VCRowInvariant A B C D E
  ) <->
  A. x e. ZZ
    A. y e. ZZ
      (
        (
          0 <_ x
          /\
          x < C
        )
        ->
        (
          (
            0 <_ y
            /\
            y < C
          )
          ->
          (
            (
              x < E
              ->
              (
                (
                  NTP4VCEntry B x y
                )
                =
                1
                <->
                ( NTP4VCPath A x y ( D + 1 ) )
              )
            )
            /\
            (
              -. x < E
              ->
              (
                (
                  NTP4VCEntry B x y
                )
                =
                1
                <->
                ( NTP4VCPath A x y D )
              )
            )
          )
        )
      ) $.
$}

${
  $d x y A B C D E F $.

  ntp4vc-column-invariant-definition $a |- (
    NTP4VCColumnInvariant A B C D E F
  ) <->
  A. x e. ZZ
    A. y e. ZZ
      (
        (
          0 <_ x
          /\
          x < C
        )
        ->
        (
          (
            0 <_ y
            /\
            y < C
          )
          ->
          (
            (
              (
                x < E
                \/
                (
                  x = E
                  /\
                  y < F
                )
              )
              ->
              (
                (
                  NTP4VCEntry B x y
                )
                =
                1
                <->
                ( NTP4VCPath A x y ( D + 1 ) )
              )
            )
            /\
            (
              -.
              (
                x < E
                \/
                (
                  x = E
                  /\
                  y < F
                )
              )
              ->
              (
                (
                  NTP4VCEntry B x y
                )
                =
                1
                <->
                ( NTP4VCPath A x y D )
              )
            )
          )
        )
      ) $.
$}

ntp4vc-next-value-definition $a |- (
  NTP4VCNextValue A B C D E
) <->
(
  (
    ( NTP4VCEntry A B C ) = 1
    ->
    E = 1
  )
  /\
  (
    -. ( NTP4VCEntry A B C ) = 1
    ->
    (
      (
        ( NTP4VCEntry A B D ) = 1
        ->
        E = ( NTP4VCEntry A D C )
      )
      /\
      (
        -. ( NTP4VCEntry A B D ) = 1
        ->
        E = 0
      )
    )
  )
) $.

${
  $d t v A B C D E F $.

  ntp4vc-cell-definition $a |- (
    NTP4VCCell A B C D E F
  ) <->
  (
    ( NTP4VCValidIndex B E F )
    /\
    (
      (
        -. ( NTP4VCEntry B E F ) = 1
        ->
        (
          ( NTP4VCValidIndex B E D )
          /\
          (
            ( NTP4VCEntry B E D ) = 1
            ->
            ( NTP4VCValidIndex B D F )
          )
        )
      )
      /\
      A. v e. { 0 , 1 }
        (
          ( NTP4VCNextValue B E F D v )
          ->
          (
            ( NTP4VCValidIndex B E F )
            /\
            A. t e. NTP4VCMatrix
              (
                ( NTP4VCSameShape t B )
                ->
                (
                  ( NTP4VCMatrixUpdate t B E F v )
                  ->
                  (
                    NTP4VCColumnInvariant
                      A t C D E ( F + 1 )
                  )
                )
              )
          )
        )
    )
  ) $.
$}

${
  $d j t A B C D E $.

  ntp4vc-column-loop-definition $a |- (
    NTP4VCColumnLoop A B C D E
  ) <->
  (
    (
      0 <_ ( ( C - 1 ) + 1 )
      ->
      (
        ( NTP4VCColumnInvariant A B C D E 0 )
        /\
        A. t e. NTP4VCMatrix
          (
            ( NTP4VCSameShape t B )
            ->
            (
              A. j e. ZZ
                (
                  (
                    (
                      0 <_ j
                      /\
                      j <_ ( C - 1 )
                    )
                    /\
                    (
                      NTP4VCColumnInvariant
                        A t C D E j
                    )
                  )
                  ->
                  ( NTP4VCCell A t C D E j )
                )
              /\
              (
                (
                  NTP4VCColumnInvariant
                    A t C D E ( ( C - 1 ) + 1 )
                )
                ->
                (
                  NTP4VCRowInvariant
                    A t C D ( E + 1 )
                )
              )
            )
          )
      )
    )
    /\
    (
      ( ( C - 1 ) + 1 ) < 0
      ->
      (
        NTP4VCRowInvariant
          A B C D ( E + 1 )
      )
    )
  ) $.
$}

${
  $d i t A B C D $.

  ntp4vc-row-loop-definition $a |- (
    NTP4VCRowLoop A B C D
  ) <->
  (
    (
      0 <_ ( ( C - 1 ) + 1 )
      ->
      (
        ( NTP4VCRowInvariant A B C D 0 )
        /\
        A. t e. NTP4VCMatrix
          (
            ( NTP4VCSameShape t B )
            ->
            (
              A. i e. ZZ
                (
                  (
                    (
                      0 <_ i
                      /\
                      i <_ ( C - 1 )
                    )
                    /\
                    ( NTP4VCRowInvariant A t C D i )
                  )
                  ->
                  ( NTP4VCColumnLoop A t C D i )
                )
              /\
              (
                (
                  NTP4VCRowInvariant
                    A t C D ( ( C - 1 ) + 1 )
                )
                ->
                ( NTP4VCInvariant A t C ( D + 1 ) )
              )
            )
          )
      )
    )
    /\
    (
      ( ( C - 1 ) + 1 ) < 0
      ->
      ( NTP4VCInvariant A B C ( D + 1 ) )
    )
  ) $.
$}

${
  $d k t A B C $.

  ntp4vc-outer-loop-definition $a |- (
    NTP4VCOuterLoop A B C
  ) <->
  (
    (
      0 <_ ( ( C - 1 ) + 1 )
      ->
      (
        ( NTP4VCInvariant A B C 0 )
        /\
        A. t e. NTP4VCMatrix
          (
            ( NTP4VCSameShape t B )
            ->
            (
              A. k e. ZZ
                (
                  (
                    (
                      0 <_ k
                      /\
                      k <_ ( C - 1 )
                    )
                    /\
                    ( NTP4VCInvariant A t C k )
                  )
                  ->
                  ( NTP4VCRowLoop A t C k )
                )
              /\
              (
                (
                  NTP4VCInvariant
                    A t C ( ( C - 1 ) + 1 )
                )
                ->
                ( NTP4VCInvariant A t C C )
              )
            )
          )
      )
    )
    /\
    (
      ( ( C - 1 ) + 1 ) < 0
      ->
      ( NTP4VCInvariant A B C C )
    )
  ) $.
$}

${
  $d A B $.

  $( Source matrices m and t. $)
  ntp4vc-original-matrix $e |- A e. NTP4VCMatrix $.
  ntp4vc-initial-matrix $e |- B e. NTP4VCMatrix $.

  $( Source assumptions fact0 through fact3. $)
  ntp4vc-fact0 $e |-
    ( NTP4VCRows A ) = ( NTP4VCColumns A ) $.
  ntp4vc-fact1 $e |-
    ( NTP4VCRows B ) = ( NTP4VCRows A ) $.
  ntp4vc-fact2 $e |-
    ( NTP4VCColumns B ) = ( NTP4VCColumns A ) $.
  ntp4vc-fact3 $e |- ( NTP4VCCopy B A ) $.

  ntp4vc-pearl-warshall-transitive-closure-vc $a |- (
    NTP4VCOuterLoop A B ( NTP4VCRows A )
  ) $.
$}
