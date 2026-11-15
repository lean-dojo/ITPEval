$(
  Statement-only formalization of Thousand Theorems corpus artifact Q1149022
  (thousand-theorems__metamath__Q1149022), "Fubini's theorem": for an
  integrable function from the product of two arbitrary s-finite measure
  spaces into an arbitrary real normed vector space, its Bochner integral
  over the product measure equals the iterated Bochner integral. This file
  contains no proof.
$)

$[ lib/set.mm $]

$(
  Q1149022Simple, Q1149022SimpleIntegral, and Q1149022LIntegral give the
  lower Lebesgue integral of a nonnegative extended-real-valued function.
  The simple integral uses SetMM's extended multiplication and sum, so a
  positive value on a fiber of measure +oo contributes +oo, while the empty
  sum and every zero contribution are zero.
  Q1149022SFinite says that a measure is a countable pointwise sum of finite
  measures on the same sigma-algebra.

  Q1149022ProdMeasure is the canonical product measure on SetMM's product
  sigma-algebra. Under the stated s-finiteness hypotheses it is uniquely
  characterized by integrating the measures of measurable sections.

  Q1149022AEStrong is the simple-function characterization of Lean's
  AEStronglyMeasurable predicate. Q1149022Integrable is almost-everywhere
  strong measurability together with finiteness of the lower integral of the
  pointwise norm, matching Lean's Integrable predicate on arbitrary normed
  codomains.

  Q1149022HasIntegral M W H y says that H is approximated in L1 by measurable
  finite-range functions in the domain of SetMM's simple Bochner integral,
  with their simple integrals converging to y. Q1149022Integral W M H is the
  unique such y when W is complete and H is integrable, and is the zero vector
  otherwise. This gives Lean's totalized Bochner integral directly from
  simple approximants rather than delegating to a general integral operator.

  The final declaration is the single unproved corpus $a statement. All
  preceding $a declarations are syntax or faithful definitions, and this
  database contains no $p proof statement.
$)

$c Q1149022Simple Q1149022SimpleIntegral Q1149022LIntegral
   Q1149022SFinite Q1149022ProdMeasure Q1149022Tendsto
   Q1149022AEStrong Q1149022Diff Q1149022L1Distance
   Q1149022Integrable Q1149022HasIntegral Q1149022Integral $.

q1149022-simple-syntax $a wff ( Q1149022Simple M G ) $.
q1149022-simple-integral-syntax
  $a class ( Q1149022SimpleIntegral M G ) $.
q1149022-lintegral-syntax $a class ( Q1149022LIntegral M H ) $.
q1149022-sfinite-syntax $a wff ( Q1149022SFinite M ) $.
q1149022-prod-measure-syntax
  $a class ( Q1149022ProdMeasure M N ) $.
q1149022-tendsto-syntax $a wff ( Q1149022Tendsto W S z ) $.
q1149022-aestrong-syntax $a wff ( Q1149022AEStrong M W H ) $.
q1149022-diff-syntax $a class ( Q1149022Diff M W H K ) $.
q1149022-l1-distance-syntax
  $a class ( Q1149022L1Distance M W H K ) $.
q1149022-integrable-syntax
  $a wff ( Q1149022Integrable M W H ) $.
q1149022-has-integral-syntax
  $a wff ( Q1149022HasIntegral M W H y ) $.
q1149022-integral-syntax $a class ( Q1149022Integral W M H ) $.

${
  $d G M $.

  q1149022-simple-definition $a |- (
    ( Q1149022Simple M G )
    <->
    (
      G : U. dom M --> ( 0 [,] +oo )
      /\
      (
        G e.
          (
            dom M
            MblFnM
            (
              sigaGen `
              ( TopOpen ` ( RR*s |`s ( 0 [,] +oo ) ) )
            )
          )
        /\
        ran G e. Fin
      )
    )
  ) $.
$}

${
  $d G M r $.

  q1149022-simple-integral-definition $a |- (
    Q1149022SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d G H M x y $.

  q1149022-lintegral-definition $a |- (
    Q1149022LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. G
          (
            ( Q1149022Simple M G )
            /\
            (
              A. x e. U. dom M ( G ` x ) <_ ( H ` x )
              /\
              y = ( Q1149022SimpleIntegral M G )
            )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d F M A n $.

  q1149022-sfinite-definition $a |- (
    ( Q1149022SFinite M )
    <->
    E. F e. ( ( U. ran measures ) ^m NN0 )
      (
        A. n e. NN0
          (
            dom ( F ` n ) = dom M
            /\
            ( ( F ` n ) ` U. dom M ) < +oo
          )
        /\
        A. A e. dom M
          ( M ` A )
          =
          ( sum^ ` ( n e. NN0 |-> ( ( F ` n ) ` A ) ) )
      )
  ) $.
$}

${
  $d C M N P x y $.

  q1149022-prod-measure-definition $a |- (
    Q1149022ProdMeasure M N
  ) =
    (
      iota_ P e. U. ran measures
        (
          dom P = ( dom M sX dom N )
          /\
          A. C e. ( dom M sX dom N )
            ( P ` C )
            =
            (
              Q1149022LIntegral
              M
              ( x e. U. dom M |->
                (
                  N `
                  { y e. U. dom N | <. x , y >. e. C }
                )
              )
            )
        )
    )
  $.
$}

${
  $d S W z $.

  q1149022-tendsto-definition $a |- (
    ( Q1149022Tendsto W S z )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) z
    )
  ) $.
$}

${
  $d H M N S W n x $.

  q1149022-aestrong-definition $a |- (
    ( Q1149022AEStrong M W H )
    <->
    (
      H e. ( ( Base ` W ) ^m U. dom M )
      /\
      E. S e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            (
              ( S ` n )
                e. ( dom M MblFnM ( sigaGen ` ( TopOpen ` W ) ) )
              /\
              ran ( S ` n ) e. Fin
            )
          /\
          E. N e. dom M
            (
              ( M ` N ) = 0
              /\
              A. x e. ( U. dom M \ N )
                (
                  Q1149022Tendsto
                  W
                  ( n e. NN0 |-> ( ( S ` n ) ` x ) )
                  ( H ` x )
                )
            )
        )
    )
  ) $.
$}

${
  $d H K M W x $.

  q1149022-diff-definition $a |- (
    Q1149022Diff M W H K
  ) =
    ( x e. U. dom M |->
      (
        ( H ` x )
        ( +g ` W )
        ( ( -g ` W ) ` ( K ` x ) )
      )
    )
  $.
$}

${
  $d H K M W x $.

  q1149022-l1-distance-definition $a |- (
    Q1149022L1Distance M W H K
  ) =
    (
      Q1149022LIntegral
      M
      ( x e. U. dom M |->
        (
          ( norm ` W )
          `
          ( ( Q1149022Diff M W H K ) ` x )
        )
      )
    )
  $.
$}

${
  $d H M W x $.

  q1149022-integrable-definition $a |- (
    ( Q1149022Integrable M W H )
    <->
    (
      ( Q1149022AEStrong M W H )
      /\
      (
        Q1149022LIntegral
        M
        ( x e. U. dom M |->
          ( ( norm ` W ) ` ( H ` x ) )
        )
      )
      < +oo
    )
  ) $.
$}

${
  $d H M S W n y $.

  q1149022-has-integral-definition $a |- (
    ( Q1149022HasIntegral M W H y )
    <->
    (
      y e. ( Base ` W )
      /\
      E. S e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            ( ( S ` n ) e. dom ( W sitg M ) )
          /\
          (
            Q1149022Tendsto
            ( RR*s |`s ( 0 [,] +oo ) )
            ( n e. NN0 |->
              ( Q1149022L1Distance M W H ( S ` n ) ) )
            0
            /\
            Q1149022Tendsto
            W
            ( n e. NN0 |-> ( ( W sitg M ) ` ( S ` n ) ) )
            y
          )
        )
    )
  ) $.
$}

${
  $d H M W y $.

  q1149022-integral-definition $a |- (
    Q1149022Integral W M H
    =
    if
    (
      (
        W e. CMetSp
        /\
        ( Q1149022Integrable M W H )
      ) ,
      (
        iota_ y e. ( Base ` W )
          ( Q1149022HasIntegral M W H y )
      ) ,
      ( 0g ` W )
    )
  ) $.
$}

${
  $d F M N W w x y $.

  thousand-theorems-q1149022-fubini $a |-
    A. M e. U. ran measures
      A. N e. U. ran measures
        A. W e. { w e. NrmVec | ( Scalar ` w ) = RRfld }
          A. F e.
            (
              ( Base ` W )
              ^m
              ( U. dom M X. U. dom N )
            )
            (
              (
                (
                  ( Q1149022SFinite M )
                  /\
                  ( Q1149022SFinite N )
                )
                /\
                (
                  Q1149022Integrable
                  ( Q1149022ProdMeasure M N )
                  W
                  F
                )
              )
              ->
              (
                Q1149022Integral
                W
                ( Q1149022ProdMeasure M N )
                F
              )
              =
              (
                Q1149022Integral
                W
                M
                ( x e. U. dom M |->
                  (
                    Q1149022Integral
                    W
                    N
                    ( y e. U. dom N |->
                      ( F ` <. x , y >. )
                    )
                  )
                )
              )
            )
  $.
$}
