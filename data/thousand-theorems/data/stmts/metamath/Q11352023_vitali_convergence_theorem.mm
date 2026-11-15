$(
  Statement-only formalization of Thousand Theorems corpus artifact Q11352023
  (thousand-theorems__metamath__Q11352023), "Vitali convergence theorem":
  for a sequence and limit in L^p over an arbitrary measure space, convergence
  in measure together with uniform integrability and uniform tightness is
  equivalent to convergence in L^p. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  M ranges over arbitrary SetMM measures and W over arbitrary normed Abelian
  groups, matching Lean's measure spaces and NormedAddCommGroup codomain.
  Since the theorem assumes 1 <= p and p != infinity, p is represented by its
  unique finite real value in [1,infinity), canonically equivalent to the
  corresponding extended nonnegative real.

  Q11352023Simple and Q11352023SimpleIntegral give the usual nonnegative
  measurable simple functions and their integrals. Q11352023LIntegral is the
  lower Lebesgue integral, and Q11352023ELpNorm is the p-th root of the lower
  integral of the p-th power of the pointwise norm. Q11352023Measure is the
  outer measure induced by M, so it applies to arbitrary subsets exactly as a
  Lean measure does.

  The remaining definitions expand almost-everywhere strong measurability,
  MemLp, convergence in measure, uniform integrability, uniform tightness, and
  convergence of the L^p norm to zero. The final declaration is the single
  unproved corpus $a statement. All preceding $a declarations are syntax or
  faithful definitions, and this database contains no $p proof statement.
$)

$c Q11352023Simple Q11352023SimpleIntegral Q11352023LIntegral
   Q11352023Measure Q11352023Indicator Q11352023Diff Q11352023Tendsto
   Q11352023AEStrong Q11352023ELpNorm Q11352023MemLp
   Q11352023InMeasure Q11352023UnifIntegrable Q11352023UnifTight
   Q11352023TendstoLpZero $.

q11352023-simple-syntax $a wff ( Q11352023Simple M G ) $.
q11352023-simple-integral-syntax
  $a class ( Q11352023SimpleIntegral M G ) $.
q11352023-lintegral-syntax $a class ( Q11352023LIntegral M H ) $.
q11352023-measure-syntax $a class ( Q11352023Measure M A ) $.
q11352023-indicator-syntax
  $a class ( Q11352023Indicator M W A H ) $.
q11352023-diff-syntax $a class ( Q11352023Diff M W H K ) $.
q11352023-tendsto-syntax $a wff ( Q11352023Tendsto W S z ) $.
q11352023-aestrong-syntax $a wff ( Q11352023AEStrong M W H ) $.
q11352023-elp-norm-syntax
  $a class ( Q11352023ELpNorm M W p H ) $.
q11352023-mem-lp-syntax $a wff ( Q11352023MemLp M W p H ) $.
q11352023-in-measure-syntax
  $a wff ( Q11352023InMeasure M W F G ) $.
q11352023-unif-integrable-syntax
  $a wff ( Q11352023UnifIntegrable M W p F ) $.
q11352023-unif-tight-syntax
  $a wff ( Q11352023UnifTight M W p F ) $.
q11352023-tendsto-lp-zero-syntax
  $a wff ( Q11352023TendstoLpZero M W p F G ) $.

${
  $d G M $.

  q11352023-simple-definition $a |- (
    ( Q11352023Simple M G )
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

  q11352023-simple-integral-definition $a |- (
    Q11352023SimpleIntegral M G
  ) =
    sum* r e. ( ran G \ { 0 } )
      ( r *e ( M ` ( `' G " { r } ) ) )
  $.
$}

${
  $d H M g x y $.

  q11352023-lintegral-definition $a |- (
    Q11352023LIntegral M H
  ) =
    sup
    (
      { y e. RR* |
        E. g
          (
            ( Q11352023Simple M g )
            /\
            (
              A. x e. U. dom M ( g ` x ) <_ ( H ` x )
              /\
              y = ( Q11352023SimpleIntegral M g )
            )
          )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d A M $.

  q11352023-measure-definition $a |- (
    Q11352023Measure M A
  ) = ( ( toOMeas ` M ) ` A ) $.
$}

${
  $d A H M W x $.

  q11352023-indicator-definition $a |- (
    Q11352023Indicator M W A H
  ) =
    ( x e. U. dom M |->
      if
      (
        x e. A ,
        ( H ` x ) ,
        ( 0g ` W )
      )
    )
  $.
$}

${
  $d H K M W x $.

  q11352023-diff-definition $a |- (
    Q11352023Diff M W H K
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
  $d S W z $.

  q11352023-tendsto-definition $a |- (
    ( Q11352023Tendsto W S z )
    <->
    (
      S : NN0 --> ( Base ` W )
      /\
      S ( ~~>t ` ( TopOpen ` W ) ) z
    )
  ) $.
$}

${
  $d H M W a f n x $.

  q11352023-aestrong-definition $a |- (
    ( Q11352023AEStrong M W H )
    <->
    (
      H e. ( ( Base ` W ) ^m U. dom M )
      /\
      E. f e. ( ( ( Base ` W ) ^m U. dom M ) ^m NN0 )
        (
          A. n e. NN0
            (
              ( f ` n )
                e. ( dom M MblFnM ( sigaGen ` ( TopOpen ` W ) ) )
              /\
              ran ( f ` n ) e. Fin
            )
          /\
          E. a e. dom M
            (
              ( M ` a ) = 0
              /\
              A. x e. ( U. dom M \ a )
                (
                  Q11352023Tendsto
                  W
                  ( n e. NN0 |-> ( ( f ` n ) ` x ) )
                  ( H ` x )
                )
            )
        )
    )
  ) $.
$}

${
  $d H M W p x y $.

  q11352023-elp-norm-definition $a |- (
    Q11352023ELpNorm M W p H
  ) =
    sup
    (
      { y e. ( 0 [,) +oo ) |
        ( y ^c p )
        <_
        (
          Q11352023LIntegral
          M
          ( x e. U. dom M |->
            ( ( ( norm ` W ) ` ( H ` x ) ) ^c p )
          )
        )
      } ,
      RR* ,
      <
    )
  $.
$}

${
  $d H M W p $.

  q11352023-mem-lp-definition $a |- (
    ( Q11352023MemLp M W p H )
    <->
    (
      ( Q11352023AEStrong M W H )
      /\
      ( Q11352023ELpNorm M W p H ) < +oo
    )
  ) $.
$}

${
  $d F G M W d e k n x $.

  q11352023-in-measure-definition $a |- (
    ( Q11352023InMeasure M W F G )
    <->
    A. e e. ( 0 (,) +oo ) A. d e. ( 0 (,) +oo )
      E. n e. NN0 A. k e. NN0
        (
          n <_ k
          ->
          (
            Q11352023Measure
            M
            { x e. U. dom M |
              e <_
                (
                  ( norm ` W )
                  `
                  (
                    (
                      Q11352023Diff
                      M
                      W
                      ( F ` k )
                      G
                    )
                    `
                    x
                  )
                )
            }
          )
          <_
          d
        )
  ) $.
$}

${
  $d F M W a d e n p $.

  q11352023-unif-integrable-definition $a |- (
    ( Q11352023UnifIntegrable M W p F )
    <->
    A. e e. ( 0 (,) +oo )
      E. d e. ( 0 (,) +oo )
        A. n e. NN0 A. a e. dom M
          (
            ( M ` a ) <_ d
            ->
            (
              Q11352023ELpNorm
              M
              W
              p
              ( Q11352023Indicator M W a ( F ` n ) )
            )
            <_
            e
          )
  ) $.
$}

${
  $d F M W a e n p $.

  q11352023-unif-tight-definition $a |- (
    ( Q11352023UnifTight M W p F )
    <->
    A. e e. ( 0 (,) +oo )
      E. a e. ~P ( U. dom M )
        (
          ( Q11352023Measure M a ) =/= +oo
          /\
          A. n e. NN0
            (
              Q11352023ELpNorm
              M
              W
              p
              (
                Q11352023Indicator
                M
                W
                ( U. dom M \ a )
                ( F ` n )
              )
            )
            <_
            e
        )
  ) $.
$}

${
  $d F G M W e k n p $.

  q11352023-tendsto-lp-zero-definition $a |- (
    ( Q11352023TendstoLpZero M W p F G )
    <->
    A. e e. ( 0 (,) +oo )
      E. n e. NN0 A. k e. NN0
        (
          n <_ k
          ->
          (
            Q11352023ELpNorm
            M
            W
            p
            ( Q11352023Diff M W ( F ` k ) G )
          )
          <_
          e
        )
  ) $.
$}

${
  $d f g m n p w $.

  thousand-theorems-q11352023-vitali-convergence $a |-
    A. m e. U. ran measures
      A. w e. ( NrmGrp i^i Abel )
        A. p e. ( 1 [,) +oo )
          A. f e. ( ( ( Base ` w ) ^m U. dom m ) ^m NN0 )
            A. g e. ( ( Base ` w ) ^m U. dom m )
              (
                (
                  A. n e. NN0
                    ( Q11352023MemLp m w p ( f ` n ) )
                  /\
                  ( Q11352023MemLp m w p g )
                )
                ->
                (
                  (
                    ( Q11352023InMeasure m w f g )
                    /\
                    (
                      ( Q11352023UnifIntegrable m w p f )
                      /\
                      ( Q11352023UnifTight m w p f )
                    )
                  )
                  <->
                  ( Q11352023TendstoLpZero m w p f g )
                )
              )
  $.
$}
