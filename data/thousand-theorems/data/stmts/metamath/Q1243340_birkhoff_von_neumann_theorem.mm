$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1243340
  (thousand-theorems__metamath__Q1243340), "Birkhoff-Von Neumann theorem":
  over every linearly ordered field and every finite index carrier, the set of
  doubly stochastic square matrices is the convex hull of the permutation
  matrices. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  QBVNPerm R N is the set of permutation matrices over the ordered field R
  indexed by the finite set N. A permutation is represented by a bijection
  s : N -1-1-onto-> N, and its matrix has entry one exactly in column s(i)
  of row i and zero elsewhere.

  QBVNDS R N is the set of matrices over R with nonnegative entries and with
  every row sum and every column sum equal to one.

  QBVNConvex R N S is the set of all finite convex combinations of members of
  S. The finite coefficient carrier W and the coefficient and point functions
  remain internally existentially quantified. This finite-combination
  characterization is bidirectionally equivalent to convexHull R S over a
  linear ordered field, including when N is empty.

  The final declaration is the single unproved $a corpus statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c QBVNPerm QBVNDS QBVNConvex $.

qbvn-permutation-matrices-syntax $a class ( QBVNPerm R N ) $.
qbvn-doubly-stochastic-syntax $a class ( QBVNDS R N ) $.
qbvn-convex-hull-syntax $a class ( QBVNConvex R N S ) $.

${
  $d M N R i j s $.

  qbvn-permutation-matrices-definition $a |- ( QBVNPerm R N ) =
    {
      M e. ( Base ` ( N Mat R ) ) |
        E. s
          (
            s : N -1-1-onto-> N
            /\
            A. i e. N A. j e. N
              ( i M j )
              =
              if (
                ( s ` i ) = j
                ,
                ( 1r ` R )
                ,
                ( 0g ` R )
              )
          )
    }
  $.
$}

${
  $d M N R i j $.

  qbvn-doubly-stochastic-definition $a |- ( QBVNDS R N ) =
    {
      M e. ( Base ` ( N Mat R ) ) |
        (
          A. i e. N A. j e. N
            ( 0g ` R ) ( le ` R ) ( i M j )
          /\
          (
            A. i e. N
              (
                R gsum
                  ( j e. N |-> ( i M j ) )
              )
              =
              ( 1r ` R )
            /\
            A. j e. N
              (
                R gsum
                  ( i e. N |-> ( i M j ) )
              )
              =
              ( 1r ` R )
          )
        )
    }
  $.
$}

${
  $d M N R S W c i j k p $.

  qbvn-convex-hull-definition $a |- ( QBVNConvex R N S ) =
    {
      M e. ( Base ` ( N Mat R ) ) |
        E. W e. Fin
          E. c e. ( ( Base ` R ) ^m W )
            E. p e. ( S ^m W )
              (
                A. k e. W
                  ( 0g ` R ) ( le ` R ) ( c ` k )
                /\
                (
                  (
                    R gsum
                      ( k e. W |-> ( c ` k ) )
                  )
                  =
                  ( 1r ` R )
                  /\
                  A. i e. N A. j e. N
                    ( i M j )
                    =
                    (
                      R gsum
                        (
                          k e. W |->
                            (
                              ( c ` k )
                              ( .r ` R )
                              ( i ( p ` k ) j )
                            )
                        )
                    )
                )
              )
    }
  $.
$}

${
  $d N R $.

  thousand-theorems-q1243340-birkhoff-von-neumann $a |-
    A. R e. oField
      A. N e. Fin
        ( QBVNDS R N )
        =
        ( QBVNConvex R N ( QBVNPerm R N ) )
  $.
$}
