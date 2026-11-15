$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1038716
  (thousand-theorems__metamath__Q1038716), "Identity theorem": two functions
  from an arbitrary nontrivially normed field to an arbitrary normed vector
  space that are analytic on neighborhoods of a preconnected set and agree
  frequently in a punctured neighborhood of a point of the set agree
  everywhere on the set. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  QIDDiff is field subtraction. QIDTerm and QIDPartial are respectively a
  coefficient term and a finite partial sum of a one-variable vector-valued
  power series. QIDAnalytic says that at every point of U, the function has a
  power-series expansion converging on a positive-radius ball. For a function
  on the one-dimensional space K, this coefficient-sequence formulation is
  equivalent to the continuous multilinear-map formulation of
  AnalyticOnNhd used by the Lean source.

  The final $a assertion quantifies over bundled SetMM normed fields and
  normed vector spaces. The existential element of norm greater than one is
  the explicit SetMM rendering of Lean's nontrivial-norm field assumption.
  Connectedness is imposed on the subspace topology. The last hypothesis says
  every open neighborhood of z contains a distinct point where F and G agree,
  exactly rendering frequent equality in the punctured neighborhood filter.
  The assertion is unproved and adds no $p proof statement.
$)

$c QIDDiff QIDTerm QIDPartial QIDAnalytic $.

qid-diff-syntax $a class ( QIDDiff K X Y ) $.
qid-term-syntax $a class ( QIDTerm K W A X Y N ) $.
qid-partial-syntax $a class ( QIDPartial K W A X Y M ) $.
qid-analytic-syntax $a wff ( QIDAnalytic K W F U ) $.

${
  $d K X Y $.

  qid-diff-definition $a |- ( QIDDiff K X Y ) =
    ( Y ( +g ` K ) ( ( -g ` K ) ` X ) )
  $.
$}

${
  $d A K N W X Y $.

  qid-term-definition $a |- ( QIDTerm K W A X Y N ) =
    (
      (
        N
        ( .g ` ( mulGrp ` K ) )
        ( QIDDiff K X Y )
      )
      ( .s ` W )
      ( A ` N )
    )
  $.
$}

${
  $d A K M W X Y n $.

  qid-partial-definition $a |- ( QIDPartial K W A X Y M ) =
    (
      W
      gsum
      (
        n e. ( 0 ... M ) |->
        ( QIDTerm K W A X Y n )
      )
    )
  $.
$}

${
  $d A F K N U W e m r x y $.

  qid-analytic-definition $a |- (
    ( QIDAnalytic K W F U )
    <->
    A. x e. U
      E. A e. ( ( Base ` W ) ^m NN0 )
        E. r e. RR+
          A. y e. ( Base ` K )
            (
              (
                ( ( norm ` K ) ` ( QIDDiff K x y ) )
                <
                r
              )
              ->
              A. e e. RR+
                E. N e. NN0
                  A. m e. ( ZZ>= ` N )
                    (
                      (
                        ( norm ` W )
                        `
                        (
                          ( QIDPartial K W A x y m )
                          ( +g ` W )
                          (
                            ( -g ` W )
                            `
                            ( F ` y )
                          )
                        )
                      )
                      <
                      e
                    )
            )
  ) $.
$}

${
  $d F G K U W O c w x y z $.

  thousand-theorems-q1038716-identity $a |-
    A. K e. ( NrmRing i^i Field )
      A. W e. { w e. NrmVec | ( Scalar ` w ) = K }
        A. F e. ( ( Base ` W ) ^m ( Base ` K ) )
          A. G e. ( ( Base ` W ) ^m ( Base ` K ) )
            A. U e. ~P ( Base ` K )
              A. z e. U
                (
                  (
                    E. c e. ( Base ` K )
                      1 < ( ( norm ` K ) ` c )
                    /\
                    ( QIDAnalytic K W F U )
                    /\
                    ( QIDAnalytic K W G U )
                    /\
                    (
                      ( ( TopOpen ` K ) |`t U )
                      e. Conn
                    )
                    /\
                    A. O e. ( TopOpen ` K )
                      (
                        z e. O
                        ->
                        E. y e. ( O \ { z } )
                          ( F ` y ) = ( G ` y )
                      )
                  )
                  ->
                  A. x e. U
                    ( F ` x ) = ( G ` x )
                )
  $.
$}
